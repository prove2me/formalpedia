-- Prove2me | Definitions.Def_FiniteGroupTesting_LinearQuery_ExploreExtension
-- name    : FiniteGroupTesting_LinearQuery_ExploreExtension
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:55.058322+00:00
-- url     : https://prove2.me/theorems/7b21a896-665a-4e51-94a1-95dd73ec4b0b
-- title:
--   Algorithm 1: Explore-Extension
-- statement:
--   Given a stored transitive action on $H$, identity label $e\in H$ and fixed $b\notin H$, initialize the discovered queue with $H$ and the first chart with the identity. Pop each discovered point once, query $b*x$, and for a new representative $t$ query $c*t$ for every $c\in H$. Check the distinguished point, injectivity and disjointness before committing a block. Scratch membership stamps avoid clearing an ambient array for every block.
--
--   $$\widehat\gamma(\mu_t(c))=\mu_t(\gamma(c)).$$
--
--   After checking that the learned $\beta$ permutes the discovered set, copy old generators by this formula and append $\beta$. The output contains raw tables and state, with no regularity or success certificate. Every original-table access is an explicit query node. A bounded $n$-iteration implementation pads stopped loops by charged inert iterations; it has the same output and queries as Algorithm 1.
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 15–16, §3.1, Algorithm 1

import Definitions.Def_FiniteGroupTesting_LinearQuery_StoredActions

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery
open OracleRun

/-- Algorithm 1 data at a completed queue iteration. Charts not yet checked are temporary,
and are committed to this state only after all of line 15 succeeds. -/
structure ExtensionState (n : ℕ) where
  discovered : LabelSet n
  representatives : LabelSet n
  chart : Fin n → Fin n → Fin n
  block : Fin n → Fin n
  coordinate : Fin n → Fin n
  beta : Fin n → Fin n
  head : ℕ
  rejected : Bool
  scratch : Fin n → ℕ

/-- Algorithm 1, lines 1--4; initialization of RAM cells is charged separately. -/
def extensionInitial {n : ℕ} (a : StoredAction n) (e : Fin n) : ExtensionState n :=
  ⟨a.domain, (LabelSet.empty e).insert e,
    fun _ c => c, fun _ => e, id, id, 0, false, fun _ => 0⟩

/-- Read the entire prospective block (line 12), even if an earlier value was bad.
A monotonically increasing block stamp reuses the scratch membership array without clearing n cells per block. -/
def queryBlock {n : ℕ} (a : StoredAction n) (e t : Fin n)
    (D : LabelSet n) (stamp : ℕ) : ℕ → (Fin n → Fin n) → (Fin n → ℕ) → Bool →
    OracleRun n ((Fin n → Fin n) × (Fin n → ℕ) × Bool)
  | 0, mu, seen, good => pure (mu, seen, good)
  | j + 1, mu, seen, good => do
      charge 12
      let c := a.domain.labels (a.domain.count - (j + 1))
      let z ← ask c t
      let ok := good && !D.marked z && (seen z != stamp) && (c != e || z == t)
      queryBlock a e t D stamp j (Function.update mu c z) (Function.update seen z stamp) ok

/-- Commit h checked cells to the block/coordinate indices and the discovery queue. -/
def commitBlock {n : ℕ} (a : StoredAction n) (t : Fin n) (mu : Fin n → Fin n) :
    ℕ → ExtensionState n → OracleRun n (ExtensionState n)
  | 0, s => pure s
  | j + 1, s => do
      charge 12
      let c := a.domain.labels (a.domain.count - (j + 1))
      let z := mu c
      commitBlock a t mu j { s with
        discovered := s.discovered.insert z
        block := Function.update s.block z t
        coordinate := Function.update s.coordinate z c }

/-- One queue iteration of Algorithm 1; b is an argument fixed throughout the call. -/
def extensionStep {n : ℕ} (a : StoredAction n) (e b : Fin n)
    (s : ExtensionState n) : OracleRun n (ExtensionState n) := do
  charge 10
  if s.rejected || s.head ≥ s.discovered.count then return s
  let x := s.discovered.labels s.head
  let t ← ask b x
  let s := { s with head := s.head + 1, beta := Function.update s.beta x t }
  if x == e && t != b then return { s with rejected := true }
  if s.discovered.marked t then return s
  let (mu, scratch, good) ← queryBlock a e t s.discovered (s.representatives.count + 1) a.domain.count (fun _ => e)
    s.scratch true
  let s := { s with scratch := scratch }
  charge (a.domain.count + 6)
  if !good then return { s with rejected := true }
  let s := { s with representatives := s.representatives.insert t, chart := Function.update s.chart t mu }
  commitBlock a t mu a.domain.count s

/-- A prefix of the actual queue loop, used for reached-state assertions. -/
def extensionPrefix {n : ℕ} (a : StoredAction n) (e b : Fin n) :
    ℕ → OracleRun n (ExtensionState n)
  | 0 => .step (20 * n + 10) (.done (extensionInitial a e))
  | j + 1 => do
      let s ← extensionPrefix a e b j
      extensionStep a e b s

/-- Check closure and injectivity of beta by scanning the discovery array. -/
def checkBeta {n : ℕ} : ℕ → ExtensionState n → (Fin n → Bool) → Bool → OracleRun n Bool
  | 0, _, _, good => pure good
  | j + 1, s, seen, good => do
      charge 10
      let x := s.discovered.labels (s.discovered.count - (j + 1))
      let z := s.beta x
      checkBeta j s (Function.update seen z true) (good && s.discovered.marked z && !seen z)

/-- Copy one old generator on the checked blocks, without original-table queries. -/
def copyGenerator {n : ℕ} (a : StoredAction n) (i : ℕ) (s : ExtensionState n) :
    ℕ → (Fin n → Fin n) → OracleRun n (Fin n → Fin n)
  | 0, row => pure row
  | j + 1, row => do
      charge 12
      let x := s.discovered.labels (s.discovered.count - (j + 1))
      let z := s.chart (s.block x) (a.image i (s.coordinate x))
      copyGenerator a i s j (Function.update row x z)

def copyGenerators {n : ℕ} (a : StoredAction n) (s : ExtensionState n) :
    ℕ → (ℕ → Fin n → Fin n) → OracleRun n (ℕ → Fin n → Fin n)
  | 0, rows => pure rows
  | j + 1, rows => do
      charge 6
      let i := a.degree - (j + 1)
      let row ← copyGenerator a i s s.discovered.count id
      copyGenerators a s j (Function.update rows i row)

/-- A successful return carries raw stored images, never an assumed regularity certificate. -/
structure ExtensionOutput (n : ℕ) where
  state : ExtensionState n
  action : StoredAction n

/-- Algorithm 1, including rejecting paths and line 22. At most n distinct points can be popped.
The n-iteration loop is a bounded implementation; an exhausted nonempty queue rejects. -/
def exploreExtension {n : ℕ} (a : StoredAction n) (e b : Fin n) :
    OracleRun n (Option (ExtensionOutput n)) := do
  let s ← extensionPrefix a e b n
  charge 8
  if s.rejected || s.head < s.discovered.count then return none
  let good ← checkBeta s.discovered.count s (fun _ => false) true
  if !good then return none
  let rows ← copyGenerators a s a.degree (fun _ => id)
  let beta ← copyGenerator ⟨a.domain, 1, fun _ => id⟩ 0
    { s with chart := fun _ c => s.beta c, coordinate := id }
    s.discovered.count id
  return some ⟨s, ⟨s.discovered, a.degree + 1, Function.update rows a.degree beta⟩⟩

end FiniteGroupTesting.LinearQuery



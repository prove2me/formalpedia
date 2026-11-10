-- Prove2me | Definitions.Def_NogoodColoring1137_Main_Codes
-- name    : NogoodColoring1137_Main_Codes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T17:00:29.366752+00:00
-- url     : https://prove2.me/theorems/09a7501b-c83d-46f6-8869-c72717c2178f
-- title:
--   Dependent words, certificate tables, boxes and exact bounds
-- statement:
--   Coordinate $v$ has domain $D_v=\mathrm{Fin}(d_v)$. A word on a scope is a dependent function on exactly that scope. A code is any set of words, including the empty set. A nogood has no extension in the code. A table stores at most one word per scope; valid tables have entries only on active scopes of size at most $\ell$. Sound tables store only nogoods.
--   $$\Phi(U,W)=|\{T\subseteq U:|T|<\ell,\ W(T)\text{ undefined}\}|.$$
--   Projection retains entries avoiding the deleted coordinate. Slicing retains old entries first, then derives from a matching longer entry, otherwise leaves the scope uncertified. Code projection and slicing use actual restrictions. A box is a product of finite sides; disjointness is in the full product. Define $\sigma=\max_vd_v$, $\Phi_0=\sum_{j<\ell}\binom nj$, $M=\sum_{j\le\ell}\binom nj$, $K=\lfloor\ln\Phi_0/\ln(\sigma/(\sigma-1))\rfloor$, and the exact binomial family bound.
--
--   These definitions are reusable for implicit codes. **Formalization Note** The empty scope is included. LogK is a specification under the theorem's positive-domain and scope hypotheses, never an executable real-log oracle.
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), §§2.1.2,4.1–4.3, pp.5,10–13

import Mathlib

namespace NogoodColoring1137.Main

/-- Finite heterogeneous domains, labeled independently at each coordinate. -/
abbrev Word {n : ℕ} (d : Fin n → ℕ) (U : Finset (Fin n)) :=
  (v : U) → Fin (d v.val)

abbrev Code {n : ℕ} (d : Fin n → ℕ) (U : Finset (Fin n)) := Set (Word d U)

/-- A certificate is not required to be a locally valid solution. -/
def Nogood {n : ℕ} {d : Fin n → ℕ} {U : Finset (Fin n)}
    (Q : Code d U) (T : Finset (Fin n)) (s : Word d T) : Prop :=
  ¬ ∃ x ∈ Q, ∀ (v : Fin n) (hT : v ∈ T) (hU : v ∈ U), x ⟨v,hU⟩ = s ⟨v,hT⟩

/-- Outside-active scopes have no semantic role; table validity explicitly clears them. -/
abbrev Table {n : ℕ} (d : Fin n → ℕ) :=
  (T : Finset (Fin n)) → Option (Word d T)

def TableValid {n : ℕ} {d : Fin n → ℕ} (ell : ℕ)
    (U : Finset (Fin n)) (W : Table d) : Prop :=
  ∀ T, ¬ (T ⊆ U ∧ T.card ≤ ell) → W T = none

def Sound {n : ℕ} {d : Fin n → ℕ} {U : Finset (Fin n)}
    (Q : Code d U) (W : Table d) : Prop :=
  ∀ T, T ⊆ U → ∀ s, W T = some s → Nogood Q T s

def CompleteAt {n : ℕ} {d : Fin n → ℕ} (ell : ℕ)
    (U : Finset (Fin n)) (W : Table d) : Prop :=
  ∀ T, T ⊆ U → T.card = ell → (W T).isSome

/-- Equation (3): strictly smaller scopes, with the empty scope included. -/
def Potential {n : ℕ} {d : Fin n → ℕ} (ell : ℕ)
    (U : Finset (Fin n)) (W : Table d) : ℕ :=
  (U.powerset.filter (fun T => T.card < ell ∧ (W T).isNone)).card

def ProjectTable {n : ℕ} {d : Fin n → ℕ} (v : Fin n) (W : Table d) : Table d :=
  fun T => if v ∈ T then none else W T

/-- §4.1 priority (i), then (ii), then (iii); no new nogood is guessed. -/
def SliceTable {n : ℕ} {d : Fin n → ℕ} (v : Fin n) (b : Fin (d v))
    (W : Table d) : Table d := fun T =>
  if v ∈ T then none else
    match W T with
    | some s => some s
    | none => match W (insert v T) with
      | none => none
      | some s => if s ⟨v, by simp⟩ = b then
          some (fun x => s ⟨x.val, Finset.mem_insert_of_mem x.property⟩)
        else none

def ProjectCode {n : ℕ} {d : Fin n → ℕ} {U : Finset (Fin n)}
    (v : Fin n) (Q : Code d U) : Code d (U.erase v) :=
  {y | ∃ x ∈ Q, ∀ z : U.erase v, x ⟨z.val, (Finset.mem_erase.mp z.property).2⟩ = y z}

def SliceCode {n : ℕ} {d : Fin n → ℕ} {U : Finset (Fin n)}
    (v : U) (b : Fin (d v.val)) (Q : Code d U) : Code d (U.erase v.val) :=
  {y | ∃ x ∈ Q, x v = b ∧
    ∀ z : U.erase v.val, x ⟨z.val, (Finset.mem_erase.mp z.property).2⟩ = y z}

abbrev Box {n : ℕ} (d : Fin n → ℕ) := (v : Fin n) → Finset (Fin (d v))

def InBox {n : ℕ} {d : Fin n → ℕ} (B : Box d) (x : (v : Fin n) → Fin (d v)) : Prop :=
  ∀ v, x v ∈ B v

def BoxDisjoint {n : ℕ} {d : Fin n → ℕ} (B B' : Box d) : Prop :=
  ∀ x, ¬ (InBox B x ∧ InBox B' x)

def Sigma {n : ℕ} (d : Fin n → ℕ) : ℕ := Finset.univ.sup d

def PhiZero (n ell : ℕ) : ℕ := ∑ j ∈ Finset.range ell, n.choose j

def ScopeCount (n ell : ℕ) : ℕ := ∑ j ∈ Finset.range (ell + 1), n.choose j

/-- Source equation (8); executable evaluation is specified separately by integer inequalities. -/
noncomputable def LogK (n ell sigma : ℕ) : ℕ :=
  ⌊Real.log (PhiZero n ell) / Real.log ((sigma : ℝ) / (sigma - 1 : ℕ))⌋₊

def FamilyBound (n K : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (min K n + 1), n.choose j

end NogoodColoring1137.Main



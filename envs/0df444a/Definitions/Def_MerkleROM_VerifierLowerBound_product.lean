-- Prove2me | Definitions.Def_MerkleROM_VerifierLowerBound_product
-- name    : MerkleROM_VerifierLowerBound_product
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T22:30:31.662135+00:00
-- url     : https://prove2.me/theorems/1aeea471-04a6-4d95-aa00-9dd16e4cad08
-- title:
--   Arbitrary-domain disjoint witnesses and the ideal greedy coupling
-- statement:
--   Let $X$ be any set. A local verifier receives a finite set $W\subseteq X$ of at most $k$ points and the oracle values on precisely those points. Search algorithms are distributions over adaptive probe trees. Single-solution and multiple-solution success are computed by running the search and evaluating its returned sets with consistent lazy oracle answers. Evaluation queries do not change the original search budget. Multiple success requires pairwise disjoint accepted sets, without assuming the search has queried its output.
--
--   For the local proof lemmas only, a normalized tree has no repeated query along a path and has queried every output point. Its fresh uniform leaf law defines good leaves, with actual good-leaf probability $\delta$. The ideal leaf law is this law conditioned on goodness. At a vertex with answer history $v$,
--
--   $$\mu_v(y)=\frac{\Pr[\mathrm{good}\wedge\mathrm{reach}\,vy]}{\Pr[\mathrm{good}\wedge\mathrm{reach}\,v]}.$$
--
--   The greedy coupling is specified through the source's reverse sampling description: conditional on the ideal answer $y$, the real answer agrees with probability $\min\{1,2^{-\lambda}/\mu_v(y)\}$ and otherwise follows the uniform-law deficit weights. Independent draws are made at successive vertices. The joint law retains the ideal leaf and the real finite query table, so conditional agreement probabilities are calculated from this coupling, not asserted as fields.
--
--   The definitions also compute $r_i=2^{-\lambda}/\mu_{v_i}(y_i)$ and $a_j=\prod_{i:\ell(v_i)\in W_j}\min\{1,r_i\}$. Defaults at zero conditional mass are explicit and cannot occur on a supported good path. No positive-$\delta$, nonempty-$X$, finite-$X$, or positive-$t$ restriction is imposed on the main disjoint product experiment.
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, pp.24–27, §6 and §6.1–6.2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Definitions.Def_MerkleROM_VerifierLowerBound_oracle

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

variable {X A : Type} {lam t k : ℕ}

/-- The verifier sees exactly the values on its input set, never the rest of the oracle. -/
abbrev SetVerifier (X : Type) (lam : ℕ) := (W : Finset X) → (W → Bits lam) → Bool

def defaultTableOracle (T : Table X (Bits lam)) : X → Bits lam := by
  classical
  exact fun q => (T.lookup q).getD (fun _ => false)

def setAccepted (V : SetVerifier X lam) (k : ℕ) (W : Finset X)
    (T : Table X (Bits lam)) : Prop :=
  W.card ≤ k ∧ V W (fun q => defaultTableOracle T q) = true

def disjointSets (Ws : Fin t → Finset X) : Prop :=
  ∀ i j, i ≠ j → Disjoint (Ws i) (Ws j)

def allPoints (Ws : Fin t → Finset X) : Finset X := by
  classical
  exact Finset.univ.biUnion Ws

/-- Output evaluation queries are part of the probability experiment, not charged to
its search budget. The Q+tk premise charges them in the single-solution reduction. -/
def multiProbability (V : SetVerifier X lam) (k : ℕ)
    (A : PMF (Tree X (Bits lam) (Fin t → Finset X))) : ℝ := by
  classical
  let checked := A.map fun a => treeBind a fun Ws =>
    treeMap (fun T => (Ws,T)) (readQueries (allPoints Ws).toList)
  exact probability (randomRun checked) fun z =>
    disjointSets z.1.1 ∧ ∀ j, setAccepted V k (z.1.1 j) z.1.2

def singleProbability (V : SetVerifier X lam) (k : ℕ)
    (A : PMF (Tree X (Bits lam) (Finset X))) : ℝ := by
  classical
  let checked := A.map fun a => treeBind a fun W =>
    treeMap (fun T => (W,T)) (readQueries W.toList)
  exact probability (randomRun checked) fun z => setAccepted V k z.1.1 z.1.2

abbrev ProductLeaf (X : Type) (lam t : ℕ) :=
  (Fin t → Finset X) × Table X (Bits lam)

/-- Syntactic path law with fresh uniform replies. Used only for normalized trees. -/
def freshLeaves : Tree X (Bits lam) A → PMF (A × Table X (Bits lam))
  | .done a => pure (a,[])
  | .probe x next => (PMF.uniformOfFintype (Bits lam)).bind fun y =>
      (freshLeaves (next y)).map fun out => (out.1,(x,y)::out.2)

/-- These are precisely Section 6's proof normalizations; the main product lemma
below quantifies over all algorithms and does NOT assume them. -/
def ProductNormalized (D : Tree X (Bits lam) (Fin t → Finset X)) : Prop :=
  ∀ tau ∈ (freshLeaves D).support,
    (tau.2.map Prod.fst).Nodup ∧ ∀ j, tau.1 j ⊆ tableDomain tau.2

def GoodLeaf (V : SetVerifier X lam) (k : ℕ) (tau : ProductLeaf X lam t) : Prop :=
  disjointSets tau.1 ∧ ∀ j, setAccepted V k (tau.1 j) tau.2

def goodProbability (D : Tree X (Bits lam) (Fin t → Finset X))
    (V : SetVerifier X lam) (k : ℕ) : ℝ :=
  probability (freshLeaves D) (GoodLeaf V k)

/-- On delta=0 use the unconditioned law. Good-leaf lemmas cannot encounter that branch. -/
def idealLeaves (D : Tree X (Bits lam) (Fin t → Finset X))
    (V : SetVerifier X lam) (k : ℕ) : PMF (ProductLeaf X lam t) := by
  classical
  exact if h : ∃ tau, GoodLeaf V k tau ∧ tau ∈ (freshLeaves D).support then
    (freshLeaves D).filter {tau | GoodLeaf V k tau} h else freshLeaves D

def prefixMass (D : Tree X (Bits lam) (Fin t → Finset X))
    (V : SetVerifier X lam) (k : ℕ) (v : List (Bits lam)) : ℝ :=
  probability (freshLeaves D) fun tau => GoodLeaf V k tau ∧ v.IsPrefix (tau.2.map Prod.snd)

def mu (D : Tree X (Bits lam) (Fin t → Finset X))
    (V : SetVerifier X lam) (k : ℕ) (v : List (Bits lam)) (y : Bits lam) : ℝ :=
  prefixMass D V k (v ++ [y]) / prefixMass D V k v

def pathRatio (D : Tree X (Bits lam) (Fin t → Finset X))
    (V : SetVerifier X lam) (k : ℕ) (tau : ProductLeaf X lam t) (i : Fin tau.2.length) : ℝ :=
  (2 : ℝ)^(-(lam : ℤ)) / mu D V k ((tau.2.map Prod.snd).take i.val) (tau.2[i.val]).2

def pathAgreement (D : Tree X (Bits lam) (Fin t → Finset X))
    (V : SetVerifier X lam) (k : ℕ) (tau : ProductLeaf X lam t) (j : Fin t) : ℝ := by
  classical
  exact ∏ i : Fin tau.2.length,
    if (tau.2[i.val]).1 ∈ tau.1 j then min 1 (pathRatio D V k tau i) else 1

/-- A normalized finite weight law; bad-input fallback is outside positive good paths. -/
def weightLaw (w : Bits lam → ℝ) : PMF (Bits lam) := by
  classical
  let f := fun y => ENNReal.ofReal (w y)
  exact if h : (∑' y, f y) ≠ 0 ∧ (∑' y, f y) ≠ ⊤ then
    PMF.normalize f h.1 h.2 else pure (fun _ => false)

/-- Reverse description of the specified greedy coupling (p.25): condition on the
ideal reply, agree with probability min(1,2^-lam/mu(y)), else use deficit weights. -/
def greedyRealReply (muV : Bits lam → ℝ) (y : Bits lam) : PMF (Bits lam) := by
  classical
  let u : ℝ := (2 : ℝ)^(-(lam : ℤ))
  let deficit := fun z => max 0 (u-muV z)
  let Z := ∑ z : Bits lam, deficit z
  let agree := min 1 (u / muV y)
  exact weightLaw (fun z => (if z = y then agree else 0) + (1-agree) * deficit z / Z)

def realAlong (D : Tree X (Bits lam) (Fin t → Finset X))
    (V : SetVerifier X lam) (k : ℕ) :
    List (Bits lam) → Table X (Bits lam) → PMF (Table X (Bits lam))
  | _,[] => pure []
  | v,(q,y)::rest => (greedyRealReply (mu D V k v) y).bind fun z =>
      (realAlong D V k (v++[y]) rest).map fun tail => (q,z)::tail

def coupledLeaves (D : Tree X (Bits lam) (Fin t → Finset X))
    (V : SetVerifier X lam) (k : ℕ) : PMF (ProductLeaf X lam t × Table X (Bits lam)) :=
  (idealLeaves D V k).bind fun tau => (realAlong D V k [] tau.2).map fun R => (tau,R)

def conditionalAgreement (D : Tree X (Bits lam) (Fin t → Finset X))
    (V : SetVerifier X lam) (k : ℕ) (tau : ProductLeaf X lam t)
    (I : Finset (Fin tau.2.length)) : ℝ :=
  probability (coupledLeaves D V k) (fun z => z.1 = tau ∧
    ∀ i ∈ I, defaultTableOracle z.2 (tau.2[i.val]).1 = (tau.2[i.val]).2) /
  probability (coupledLeaves D V k) (fun z => z.1 = tau)

end MerkleROM.VerifierLowerBound



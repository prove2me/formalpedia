-- Prove2me | Definitions.Def_HardcoreSlices_roundProb
-- name    : HardcoreSlices_roundProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:54.35446+00:00
-- url     : https://prove2.me/theorems/3f8f8efc-42f9-4bf8-b59c-d6d558d5ca0b
-- title:
--   One round of the rejection sampler of §6
-- statement:
--   The labels of the slice decomposition are $(k_X,k_Y)\in\text{low}\times\text{low}$; $(k,X)$ and $(k,Y)$ for $k\in\text{med}$; and two high labels $X,Y$. Each low or medium label $j$ has an estimate $\hat Z_j$, and each high label has the exact weight
--   $$Z_X(\lambda)=(1+\lambda)^{|Y|}\sum_{k\in\text{high}}\binom{|X|}{k}\lambda^k.$$
--   With $\hat Z_G=\sum_j\hat Z_j$, a round picks label $j$ with probability $\hat Z_j/\hat Z_G$ and then proceeds by case:
--
--   1. **Label $(k_X,k_Y)$.** Build an ordered independent set $\tau$ with probability $q(\tau)$, vertex by vertex in the link; accept with probability $\lambda^{k_X+k_Y}/(4(k_X+k_Y)!\hat Z_jq(\tau))$.
--   2. **Label $(k,X)$.** Build an ordered $S\subseteq X$ of size $k$; sample $T\subseteq Y\setminus N(S)$ with each vertex present with probability $\lambda/(1+\lambda)$; accept with probability $\frac{\lambda^{k+|T|}}{4k!\hat Z_jq(\tau,T)}2^{-\mathbf 1\{|T|\in\text{med}\}}$.
--   3. **Label $X$.** Choose $K\in\text{high}$ with probability $\propto\binom{|X|}K\lambda^K$, then $S$ uniform in $\binom XK$, then $T\subseteq Y$ with each vertex present with probability $\lambda/(1+\lambda)$; return $S\cup T$ with probability $1/8$ if it is independent and $|T|$ is high, and $1/4$ if it is independent and $|T|$ is low.
--
--   `roundProb` is the probability that the round returns a given set.
--
--   **Formalization Note** The proposal $q$ is a function of the current set and the next vertex, and a sequence leaving $\mathcal X_\tau(1)$ has probability $0$. Each acceptance is `min 1` of the printed ratio. The sum runs over all orderings of the set.
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), §6, Approximate sampling, pp.29–32

import Mathlib
import Definitions.Def_HardcoreSlices_Ztilde
import Definitions.Def_HardcoreSlices_twoSidedSlice
import Definitions.Def_HardcoreSlices_oneSidedSlice
import Definitions.Def_HDXConc_linkWeight

open Classical

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- A label of the slice decomposition (Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), §6, Approximate sampling, p.29): `(kX, kY) ∈ low × low`, `(k, X)` or `(k, Y)`
for `k ∈ med`, and the two high labels `X`, `Y`. The side `false` is `X` and `true` is `Y`. -/
inductive Label where
  | two (kX kY : ℕ)
  | one (b : Bool) (k : ℕ)
  | high (b : Bool)
  deriving DecidableEq

/-- The label set of p.29. -/
noncomputable def labels (m : ℕ) (α β : ℝ) : Finset Label :=
  (((Finset.range (m + 1)).filter (IsLow α m) ×ˢ (Finset.range (m + 1)).filter (IsLow α m)).image
      (fun p => Label.two p.1 p.2)) ∪
    (((Finset.univ : Finset Bool) ×ˢ (Finset.range (m + 1)).filter (IsMed α β m)).image
      (fun p => Label.one p.1 p.2)) ∪
    {Label.high false, Label.high true}

/-- `Σ_{k∈high} (|X| choose k) λ^k`. -/
noncomputable def highSum (m : ℕ) (lam α β : ℝ) : ℝ :=
  ∑ k ∈ (Finset.range (m + 1)).filter (IsHigh α β m), (m.choose k : ℝ) * lam ^ k

/-- `Z_X(λ) = (1 + λ)^{|Y|} Σ_{k∈high} (|X| choose k) λ^k = Z_Y(λ)` (p.30). -/
noncomputable def highZ (m : ℕ) (lam α β : ℝ) : ℝ := (1 + lam) ^ m * highSum m lam α β

/-- The weight of a label: the given estimate `Ẑj` on a low or medium label, the exact `Z_X`, `Z_Y` on a high label (p.30). -/
noncomputable def labelWeight (m : ℕ) (lam α β : ℝ) (Zh : Label → ℝ) : Label → ℝ
  | .high _ => highZ m lam α β
  | ℓ => Zh ℓ

/-- `Ẑ_G(λ)`, the sum of the label weights (p.30). -/
noncomputable def ZhatG (m : ℕ) (lam α β : ℝ) (Zh : Label → ℝ) : ℝ :=
  ∑ ℓ ∈ labels m α β, labelWeight m lam α β Zh ℓ

/-- The probability `q(τ) = Π_i q_{τ_i}(v_{i+1})` of a sequence built vertex by vertex from `τ` (pp.30–31), when the vertex at
each step is drawn from `q_τ` on `Xτ(1)`. A sequence leaving `Xτ(1)` has probability `0`. -/
noncomputable def seqProb {m : ℕ} (X : Finset (Finset (Vertex m)))
    (q : Finset (Vertex m) → Vertex m → ℝ) : Finset (Vertex m) → List (Vertex m) → ℝ
  | _, [] => 1
  | τ, v :: L => (if v ∈ HDXConc.linkVerts X τ then q τ v else 0) * seqProb X q (insert v τ) L

/-- The product law on subsets `T ⊆ A`: each vertex with probability `λ/(1+λ)` independently (pp.31–32). -/
noncomputable def tLaw {m : ℕ} (lam : ℝ) (A T : Finset (Vertex m)) : ℝ :=
  if T ⊆ A then (lam / (1 + lam)) ^ T.card * (1 / (1 + lam)) ^ (A \ T).card else 0

/-- The total proposed-and-accepted probability of `I` in a round, given the label `ℓ`.

* **Case 1** (p.30–31), `ℓ = (kX, kY)`: over all orderings `L` of `I`, proposal `q(L)`, acceptance
  `λ^{kX+kY} / (4 (kX+kY)! Ẑj q(L))`.
* **Case 2** (p.31), `ℓ = (k, side)`: over all orderings `L` of `S = I ∩ side`, proposal `q(L, T) = q(L) · tLaw` with
  `T = I ∩ other side ⊆ other side \ N(S)`, acceptance `(λ^{k+|T|} / (4 k! Ẑj q(L, T))) · 2^{−1{|T|∈med}}`.
* **Case 3** (p.32), `ℓ = side`: `K ∈ high` with probability `∝ (|X| choose K) λ^K`, `S` uniform in `(X choose K)`, `T` from the
  product law on the other side, return with probability `1/8` if `S ∪ T` is independent and `|T| ∈ high`, `1/4` if independent and
  `|T| ∈ low`.

**Formalization Note.** The acceptance is `min 1` of the printed ratio, so a ratio above `1` is not a probability in disguise. -/
noncomputable def caseMass {m : ℕ} (G : SimpleGraph (Vertex m)) (lam α β : ℝ) (Zh : Label → ℝ)
    (qT : ℕ → ℕ → Finset (Vertex m) → Vertex m → ℝ) (qO : Bool → ℕ → Finset (Vertex m) → Vertex m → ℝ)
    (I : Finset (Vertex m)) : Label → ℝ
  | .two kX kY =>
      if I.card = kX + kY then
        ∑ L ∈ I.val.lists.toFinset,
          seqProb (twoSidedComplex G kX kY) (qT kX kY) ∅ L *
            min 1 (lam ^ (kX + kY) / (4 * ((kX + kY).factorial : ℝ) * Zh (.two kX kY) *
              seqProb (twoSidedComplex G kX kY) (qT kX kY) ∅ L))
      else 0
  | .one b k =>
      if (I ∩ sideOf m b).card = k then
        ∑ L ∈ (I ∩ sideOf m b).val.lists.toFinset,
          (seqProb (oneSidedComplex (sideOf m b) k) (qO b k) ∅ L *
              tLaw lam (sideOf m (!b) \ vertexBoundary G (I ∩ sideOf m b)) (I ∩ sideOf m (!b))) *
            min 1 ((lam ^ (k + (I ∩ sideOf m (!b)).card) / (4 * (k.factorial : ℝ) * Zh (.one b k) *
                (seqProb (oneSidedComplex (sideOf m b) k) (qO b k) ∅ L *
                  tLaw lam (sideOf m (!b) \ vertexBoundary G (I ∩ sideOf m b)) (I ∩ sideOf m (!b))))) *
              (1 / 2 : ℝ) ^ (if IsMed α β m (I ∩ sideOf m (!b)).card then 1 else 0))
      else 0
  | .high b =>
      if IsHigh α β m (I ∩ sideOf m b).card ∧ IsIndependent G I then
        ((m.choose (I ∩ sideOf m b).card : ℝ) * lam ^ (I ∩ sideOf m b).card / highSum m lam α β) *
          (1 / (m.choose (I ∩ sideOf m b).card : ℝ)) *
          tLaw lam (sideOf m (!b)) (I ∩ sideOf m (!b)) *
          (if IsHigh α β m (I ∩ sideOf m (!b)).card then 1 / 8
           else if IsLow α m (I ∩ sideOf m (!b)).card then 1 / 4 else 0)
      else 0

/-- **The probability that a round of the sampler returns `I`** (Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), §6, pp.29–32): the label `ℓj` with probability
`ρj = Ẑj / Ẑ_G`, then the proposal and acceptance of its case. -/
noncomputable def roundProb {m : ℕ} (G : SimpleGraph (Vertex m)) (lam α β : ℝ) (Zh : Label → ℝ)
    (qT : ℕ → ℕ → Finset (Vertex m) → Vertex m → ℝ) (qO : Bool → ℕ → Finset (Vertex m) → Vertex m → ℝ)
    (I : Finset (Vertex m)) : ℝ :=
  ∑ ℓ ∈ labels m α β, (labelWeight m lam α β Zh ℓ / ZhatG m lam α β Zh) * caseMass G lam α β Zh qT qO I ℓ

end HardcoreSlices



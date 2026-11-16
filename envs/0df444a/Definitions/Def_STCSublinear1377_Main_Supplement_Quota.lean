-- Prove2me | Definitions.Def_STCSublinear1377_Main_Supplement_Quota
-- name    : STCSublinear1377_Main_Supplement_Quota
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:20:14.808195+00:00
-- url     : https://prove2.me/theorems/bcc9f716-6327-4352-a18e-021dfbd40142
-- title:
--   Quota sets, unary vertex weights and crossing weight of a partition
-- statement:
--   For a weighted graph $Q$ with a distinguished vertex $o$, nonnegative integer vertex weights $\nu$ and an integer quota $\ell$, put
--
--   $$\mathrm{opt}(Q,o,\nu,\ell)=\min\{b_Q(C): C\subseteq V_Q,\ o\notin C,\ \nu(C)\ge\ell\}$$
--
--   (Proposition 3.6, p.11), an attained minimum over vertex subsets. For a partition $\mathcal P$ of a vertex set $U$ given by labels and $C\subseteq U$,
--
--   $$x_{\mathcal P}(C)=\omega_F\big(\{uv\in E_F: u,v\in C\text{ belong to different parts of }\mathcal P\}\big)$$
--
--   (§3.3, p.11), the total weight of edges with both ends in $C$ that join different parts. Vertex weights are encoded in unary, so the input length accounts for the total weight $W=\nu(V_Q)$.
--
--   **Formalization Note** The parts of a labelled partition of $U$ are the nonempty label classes inside $U$. The quota minimum is zero when no admissible set exists; for $\ell\le W$ the set $V_Q\setminus\{o\}$ is admissible.
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, §3.3 definition of x_P(C) and Proposition 3.6, PDF/printed p.11

import Definitions.Def_STCSublinear1377_Main_Supplement_Terminal
set_option autoImplicit false

namespace STCSublinear1377.Main.Supplement

/-- Unary encoding of a vertex weight: `ν(v)` ones and a separator for every vertex. -/
def unaryWeights {n : ℕ} (ν : Fin n → ℕ) : List Bool :=
  (List.finRange n).flatMap (fun v => List.replicate (ν v) true ++ [false])

/-- `min {b_Q(C) : o ∉ C, ν(C) ≥ ℓ}`, an attained minimum over vertex subsets; zero if no
admissible set exists. -/
noncomputable def quotaOpt {n : ℕ} (f : WeightedGraph n) (o : Fin n) (ν : Fin n → ℕ)
    (ℓ : ℕ) : ℝ := by
  classical
  let values := (f.vertices.powerset.filter
    (fun c => o ∉ c ∧ ℓ ≤ ∑ v ∈ c, ν v)).image f.boundary
  exact if h : values.Nonempty then values.min' h else 0

/-- The parts of the partition of `U` given by labels: the nonempty label classes. -/
noncomputable def labelParts {n : ℕ} (U : Finset (Fin n)) (lab : Fin n → Fin n) :
    Finset (Finset (Fin n)) := by
  classical
  exact (U.image lab).image (fun s => U.filter (fun v => lab v = s))

/-- `x_P(C)`: total weight of edges with both ends in `C` joining different parts. -/
noncomputable def crossWeight {n : ℕ} (f : WeightedGraph n) (lab : Fin n → Fin n)
    (C : Finset (Fin n)) : ℝ := by
  classical
  exact ∑ u ∈ C, ∑ v ∈ C,
    if u < v ∧ f.edges u v = true ∧ lab u ≠ lab v then f.weight u v else 0

end STCSublinear1377.Main.Supplement



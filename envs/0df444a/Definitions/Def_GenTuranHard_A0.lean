-- Prove2me | Definitions.Def_GenTuranHard_A0
-- name    : GenTuranHard_A0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:36:22.427071+00:00
-- url     : https://prove2.me/theorems/396e1305-f3fa-4d00-9f46-44ae4cbc9bdb
-- title:
--   $A_0(\mathbf x,G)$, $A_2(\mathbf x,G)$, $A_{\ge 3}(\mathbf x,G)$, $S(\mathbf x,n)$ and the exponents (4.3)
-- statement:
--   Let $T$ be a graph and $\mathbf x = (x_1, \dots, x_s)$. For a graph $Q$ let $f_Q(\mathbf x) = \sum \prod_{i=1}^{s} x_i^{|I_i|}$, the sum over the sequences satisfying (4.1) with $T_s \cong Q$. With $\mathcal Q_T$ a set of representatives of the bipartite graphs on at most $v(T)$ vertices and $n = v(G)$ (p.16),
--
--   $$
--   A_0(\mathbf x, G) = \sum_{Q \in \mathcal Q_T,\, p(Q) = 0} f_Q(\mathbf x) \hom(Q, G), \quad
--   A_2(\mathbf x, G) = \sum_{Q \in \mathcal Q_T,\, p(Q) = 2} f_Q(\mathbf x) \hom(Q, G), \quad
--   A_{\ge 3}(\mathbf x, G) = \sum_{Q \in \mathcal Q_T,\, p(Q) \ge 3} f_Q(\mathbf x) \hom(Q, G),
--   $$
--
--   $$
--   S(\mathbf x, n) = \sum_{Q \in \mathcal Q_T,\, p(Q) = 2} 2 f_Q(\mathbf x)\, n^{v(Q) - 2}.
--   $$
--
--   The exponents of (4.3) are, for $s = v(T) - 2$,
--
--   $$
--   d_s = v(T) + 3, \qquad d_i = v(T) + 3 + v(T) \sum_{j = i+1}^{s} d_j, \qquad x_i = n^{d_i} \quad (i = 1, \dots, s).
--   $$
--
--   These are the quantities in which the bounds (2.1) of the reduction are written: $L = \gamma^{-1} B^{v(T)} A_0(\mathbf x, G)$ and $S = \gamma^{-1} B^{v(T)} S(\mathbf x, n)$ (p.21).
--
--   **Formalization Note** The sums are taken directly over the sequences of (4.1) started at $T$ (renumbered on $\{0,\dots,v(T)-1\}$), grouped by $p(T_s)$, instead of over $\mathcal Q_T$; the values are equal since $\hom(\cdot, G)$, $v(\cdot)$ and $p(\cdot)$ are isomorphism-invariant. All quantities are natural numbers. The exponents are the list $[d_1, \dots, d_s]$, and $\mathbf x$ is the list $[n^{d_1}, \dots, n^{d_s}]$.
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), (4.2), p.16 (A₀, A₂, A≥3), p.16 (f_Q, S(x, n)), (4.3), p.16

import Mathlib
import Definitions.Def_GenTuranHard_validSeqs

set_option autoImplicit false

namespace GenTuranHard

open scoped Classical in
/-- **A₀(x, G)** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, (4.2), p.16): the part of
the expansion of `hom(T, L_x(G))` whose terminal graphs have no nonisolated vertex,
`A₀(x, G) = Σ_{Q ∈ 𝒬_T, p(Q) = 0} f_Q(x) hom(Q, G)`, with `f_Q(x) = Σ_{(I₁,…,I_s) satisfying (4.1),
T_s ≅ Q} ∏ x_i^{|I_i|}` and `s` the length of `x`.

**Formalization Note** The sum is taken directly over the sequences of (4.1) (started at `T` renumbered
on `Fin v(T)`), grouped by `p(T_s)`, instead of over a set `𝒬_T` of isomorphism-class representatives;
the value is the same because `hom(·, G)` and `p(·)` are isomorphism-invariant. -/
noncomputable def A0 {W : Type} [Fintype W] (T : SimpleGraph W) (x : List ℕ) (G : FinGraph) : ℕ :=
    ∑ Is ∈ (validSeqs x.length (toFin T)).filter (fun Is => pNon (termGraph (toFin T) Is) = 0),
      monoWeight x Is * homCount (termGraph (toFin T) Is).2 G.2

open scoped Classical in
/-- **A₂(x, G)** ((4.2), p.16): the part with `p(T_s) = 2`. -/
noncomputable def A2 {W : Type} [Fintype W] (T : SimpleGraph W) (x : List ℕ) (G : FinGraph) : ℕ :=
    ∑ Is ∈ (validSeqs x.length (toFin T)).filter (fun Is => pNon (termGraph (toFin T) Is) = 2),
      monoWeight x Is * homCount (termGraph (toFin T) Is).2 G.2

open scoped Classical in
/-- **A_{≥3}(x, G)** ((4.2), p.16): the part with `p(T_s) ≥ 3`. -/
noncomputable def Ages3 {W : Type} [Fintype W] (T : SimpleGraph W) (x : List ℕ) (G : FinGraph) :
    ℕ :=
    ∑ Is ∈ (validSeqs x.length (toFin T)).filter (fun Is => 3 ≤ pNon (termGraph (toFin T) Is)),
      monoWeight x Is * homCount (termGraph (toFin T) Is).2 G.2

open scoped Classical in
/-- **S(x, n)** (p.16): `S(x, n) = Σ_{Q ∈ 𝒬_T, p(Q) = 2} 2 · f_Q(x) · n^{v(Q) − 2}`, summed directly over
the sequences of (4.1) with `p(T_s) = 2` (so `v(T_s) ≥ 2` and the exponent is a genuine difference). -/
noncomputable def Sx {W : Type} [Fintype W] (T : SimpleGraph W) (x : List ℕ) (n : ℕ) : ℕ :=
    ∑ Is ∈ (validSeqs x.length (toFin T)).filter (fun Is => pNon (termGraph (toFin T) Is) = 2),
      2 * monoWeight x Is * n ^ ((termGraph (toFin T) Is).1 - 2)

/-- The exponents of (4.3) (p.16) as the list `[d₁, …, d_s]` for `v(T) = t`:
`d_s = t + 3` and `d_i = t + 3 + t · Σ_{j=i+1}^{s} d_j`. Each `d_i` depends only on the number `s − i`
of later indices, so the list for `s + 1` is the list for `s` with one new first entry. -/
def dList (t : ℕ) : ℕ → List ℕ
  | 0 => []
  | s + 1 => (t + 3 + t * (dList t s).sum) :: dList t s

/-- The vector `x = (x₁, …, x_s)` of (4.3) (p.16): `s = t − 2` with `t = v(T)`, and `x_i = n^{d_i}`. -/
def xVec (t n : ℕ) : List ℕ := (dList t (t - 2)).map (fun d => n ^ d)

end GenTuranHard



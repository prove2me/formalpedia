-- Prove2me | Definitions.Def_MultiThinkCoT_Supplement_passErr
-- name    : MultiThinkCoT_Supplement_passErr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:56:40.773581+00:00
-- url     : https://prove2.me/theorems/1513c176-fca3-4b80-85d0-613736ec486b
-- title:
--   Instance-dependent CoT supervision, the candidate set $\widehat{\mathcal Z}$ and the pass@$\kappa$ error
-- statement:
--   In instance-dependent CoT supervision (Definition 6.1) the adversary fixes an input distribution $\mathcal D$ on $\mathcal X$, generators $f_1,\dots,f_\kappa$, and a conditional distribution $\mathcal P(\cdot\mid x)$ on $[\kappa]$ before sampling. Inputs are drawn as $x^{(i)}\sim\mathcal D$ i.i.d., and conditionally on them the source identities are drawn independently as $j^{(i)}\sim\mathcal P(\cdot\mid x^{(i)})$; the observed trace is $z^{(i)}=f_{j^{(i)}}^{\mathrm{CoT}\text{-}T}(x^{(i)})$. Equivalently, the pairs $(x^{(i)},j^{(i)})$ are i.i.d. from the **joint law** of $x\sim\mathcal D$, $j\sim\mathcal P(\cdot\mid x)$.
--
--   For generators $g_1,\dots,g_\kappa$ the **candidate set** on an input $x$ is
--
--   $$
--   \widehat{\mathcal Z}(x)=\big\{g_j^{\mathrm{CoT}\text{-}T}(x):j\in[\kappa]\big\},
--   $$
--
--   and the **pass@$\kappa$ error** of a candidate-set predictor $\widehat{\mathcal Z}$ is
--
--   $$
--   \Pr_{x\sim\mathcal D,\ j\sim\mathcal P(\cdot\mid x)}\Big[f_j^{\mathrm{CoT}\text{-}T}(x)\notin\widehat{\mathcal Z}(x)\Big],
--   $$
--
--   the probability that the trace of the source actually used on a fresh input is not among the predicted candidates.
--
--   These objects state the pass@$\kappa$ results of §7.1: the generalization bound for the rule $\kappa$-ConsistentCoT (Theorem 4) and the efficient learner with known provenance (Theorem 5).
--
--   **Formalization Note** The domain is countable, so $\mathcal D$ is a probability mass function on the subtype $\mathcal X$ and $\mathcal P$ is a kernel `X → PMF (Fin κ)`. The candidate set is a finite set of strings. The pass@$\kappa$ error is the real number given by the joint-law mass of the failure set; the predictor $\widehat{\mathcal Z}$ is an arbitrary map from strings to finite sets of strings.
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Definition 6.1, p.16 (PDF p.16); rule (κ-ConsistentCoT) and the pass@κ error, §7.1, p.21 (PDF p.21)

import Mathlib
import Definitions.Def_MultiThinkCoT_e2e

namespace MultiThinkCoT.Supplement

/-!
# Instance-dependent CoT supervision, the candidate set `Ẑ` and the pass@κ error

N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…), Definition 6.1, p.16 (PDF p.16); rule (κ-ConsistentCoT) and the
pass@κ error, §7.1, p.21 (PDF p.21).

Definition 6.1: the adversary fixes `P : X → ∆([κ])` before the inputs are sampled; the inputs are
`x(i) ∼iid D`, and conditionally on them the source identities are drawn independently as
`j(i) ∼ P(· | x(i))`; the trace is `z(i) = f_{j(i)}^{CoT-T}(x(i))`. The rule (κ-ConsistentCoT)
finds `f̂_1, …, f̂_κ ∈ F` with `z(i) ∈ {f̂_j^{CoT-T}(x(i)) : j ∈ [κ]}` for all `i`, and for pass@κ
evaluation returns the candidate set `Ẑ(x) = {f̂_j^{CoT-T}(x) : j ∈ [κ]}`. The pass@κ error of a
candidate-set predictor `Ẑ` is `Pr_{x∼D, j∼P(·|x)}[f_j^{CoT-T}(x) ∉ Ẑ(x)]`.

**Formalization Note.**
* `D : PMF X` on the countable domain (as in `MultiThinkCoT.endToEndError`) and
  `P : X → PMF (Fin κ)`. The pairs `(x(i), j(i))` are then i.i.d. from the joint law
  `jointLaw D P` of `x ∼ D`, `j ∼ P(· | x)`; this is exactly the two-stage sampling of
  Definition 6.1.
* `candSet T g x` is a `Finset` of strings (each of length `T`).
* `passErr D P T f Z` is the real number `Pr_{(x,j) ∼ jointLaw D P}[f_j^{CoT-T}(x) ∉ Z(x)]`,
  where `f` are the adversary's (target) generators and `Z` is any candidate-set predictor.
-/

/-- The joint law of `(x, j)`: `x ∼ D`, then `j ∼ P(· | x)` (Definition 6.1). -/
noncomputable def jointLaw {X : Type} {κ : ℕ} (D : PMF X) (P : X → PMF (Fin κ)) :
    PMF (X × Fin κ) :=
  D.bind fun x => (P x).map fun j => (x, j)

/-- The candidate set `Ẑ(x) = {g_j^{CoT-T}(x) : j ∈ [κ]}`. -/
def candSet {κ : ℕ} (T : ℕ) (g : Fin κ → Gen) (x : List Bool) : Finset (List Bool) :=
  Finset.univ.image fun j => cot (g j) T x

/-- The pass@κ error `Pr_{x∼D, j∼P(·|x)}[f_j^{CoT-T}(x) ∉ Z(x)]` of a candidate-set predictor
`Z`, for the target generators `f`. -/
noncomputable def passErr {X : Set (List Bool)} {κ : ℕ} (D : PMF X) (P : X → PMF (Fin κ))
    (T : ℕ) (f : Fin κ → Gen) (Z : List Bool → Finset (List Bool)) : ℝ :=
  ((jointLaw D P).toOuterMeasure {q | cot (f q.2) T q.1.1 ∉ Z q.1.1}).toReal

end MultiThinkCoT.Supplement



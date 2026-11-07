-- Prove2me | Definitions.Def_VecBalPoly_GoodDir
-- name    : VecBalPoly_GoodDir
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T23:16:20.771874+00:00
-- url     : https://prove2.me/theorems/1924439a-5dbf-43c5-ad10-df03deb37419
-- title:
--   Directions with the guarantees of Lemma 2.1
-- statement:
--   At a state, a direction $h\in\mathbb R^V$ is **good** when
--   1. $\sum_{j\in T_i}a_{ij}h_j=0$ for every large row $i$;
--   2. $\langle g_{i\sigma},h\rangle=0$ for every medium row $i$ and sign $\sigma$ with $u_{i\sigma}\ge-1$ (nearly tight barriers);
--   3. $\tfrac12\le\|h\|_2\le1$;
--   4. $|\langle\nabla\Phi,h\rangle|\le\epsilon$ and $h^{\mathsf T}\nabla^2\Phi h\le-3\eta/16$, with $\epsilon=\eta\tau/K^2$.
--
--   These are the guarantees that Lemma 2.1 provides and that Algorithm 2.2 uses.
--
--   **Formalization Note** $h$ is a vector of $\mathbb R^n$ vanishing off $V$.
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Lemma 2.1, p.6 (PDF p.7); §2.2, p.4

import Mathlib
import Definitions.Def_VecBalPoly_Phi

namespace VecBalPoly

open Matrix

variable {m n : ℕ}

/-- **A direction with the guarantees of Lemma 2.1.** `h ∈ ℝ^V` satisfies
1. the large-row constraints `∑_{j∈Tᵢ} aᵢⱼhⱼ = 0`;
2. the nearly tight barrier constraints `⟨∇u_{iσ}, h⟩ = 0` for every medium row `i` and sign `σ`
   with `u_{iσ} ≥ −1`;
3. `1/2 ≤ ‖h‖₂ ≤ 1`, `|⟨∇Φ, h⟩| ≤ ϵ` and `hᵀ∇²Φh ≤ −3η/16`, with `ϵ = ητ/K²`.

Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Lemma 2.1, p.6 (PDF p.7); §2.2, p.4.

**Formalization Note** `h ∈ ℝ^V` is a vector of `ℝⁿ` vanishing off `V`. Algorithm 2.2's step 1
("compute an update direction h using Lemma 2.1") is modelled as any `h` with these properties,
so the runs of Algorithm 2.2 below quantify over all such choices. -/
def GoodDir (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) (h : Fin n → ℝ) : Prop :=
  (∀ j, j ∉ st.V → h j = 0) ∧
  (∀ i, IsLarge A st i → ∑ j ∈ st.T i, A i j * h j = 0) ∧
  (∀ i σ, IsMedium A st i → -1 ≤ u A st i σ → gradU A st i σ ⬝ᵥ h = 0) ∧
  1 / 2 ≤ Real.sqrt (∑ j, h j ^ 2) ∧ Real.sqrt (∑ j, h j ^ 2) ≤ 1 ∧
  |dPhi A st h| ≤ epsA n ∧
  d2Phi A st h ≤ -3 * eta n / 16

end VecBalPoly



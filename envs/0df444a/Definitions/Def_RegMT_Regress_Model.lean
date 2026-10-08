-- Prove2me | Definitions.Def_RegMT_Regress_Model
-- name    : RegMT_Regress_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:45.11541+00:00
-- url     : https://prove2.me/theorems/6e4a0763-08c7-460f-99bd-355faf42a484
-- title:
--   §2.1, §3.1, p. 30 — the residual functional (w, −1) on ℝ^{n+1} and the effective domain Θ of L*
-- statement:
--   This file fixes the two objects of *Regularization via Mass Transportation* (Shafieezadeh-Abadeh, Kuhn and Mohajerin Esfahani) that the regression results need beyond the Wasserstein ball and the worst-case risk.
--
--   **The residual functional.** The input-output space $\mathbb R^{n+1}$ carries an arbitrary norm $\|\cdot\|$ (§3.1). A point is $\xi=(x,y)$ with input $x\in\mathbb R^n$ and output $y\in\mathbb R$. For a weight vector $w\in\mathbb R^n$, the linear hypothesis $h(x)=\langle w,x\rangle$ has residual
--
--   $$
--   \xi=(x,y)\ \longmapsto\ \langle w,x\rangle-y=\langle (w,-1),\xi\rangle ,
--   $$
--
--   so the regression loss of §2.1 and §3.1 is $\ell(\langle w,x\rangle,y)=L(\langle (w,-1),\xi\rangle)$ for a univariate loss $L$. As a linear functional on $(\mathbb R^{n+1},\|\cdot\|)$, the vector $(w,-1)$ has the dual norm $\|(w,-1)\|_*=\sup\{\langle (w,-1),\xi\rangle:\|\xi\|\le 1\}$ of §1.1.
--
--   **The effective domain of the conjugate.** For a univariate loss $L:\mathbb R\to\mathbb R$ with convex conjugate $L^*(\theta)=\sup_{z\in\mathbb R}\theta z-L(z)$ (§1.1), the effective domain is
--
--   $$
--   \Theta=\{\theta\in\mathbb R:\ L^*(\theta)<\infty\}.
--   $$
--
--   Because $L$ is real-valued, $L^*(\theta)>-\infty$ for every $\theta$, so $\theta\in\Theta$ exactly when $z\mapsto\theta z-L(z)$ is bounded above.
--
--   These objects state the dual-norm penalty $\rho\,\mathrm{lip}(L)\,\|(w,-1)\|_*$ of Theorem 3.1(ii) and the conjugate description of the Lipschitz modulus used in the proof of Lemma A.3.
--
--   **Formalization Note.** The space $\mathbb R^{n+1}$ is an abstract real normed space $E$ with a continuous linear isomorphism $e:E\to\mathbb R^n\times\mathbb R$ that reads off input and output coordinates, so the norm of $E$ is arbitrary while $w$ and the samples stay coordinate vectors. `pairing e w` is the functional $\xi\mapsto\sum_j w_j (e\,\xi)_{1,j}-(e\,\xi)_2$, and $\|(w,-1)\|_*$ is its operator norm. `conjDom L` is $\Theta$, written through boundedness above instead of a real supremum, which would be the junk value $0$ on unbounded families. The file also contains the simp lemma `pairing_apply`. Chunk I of this series defines the same set $\Theta$ in its own namespace.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p. 4 (§1.1, dual norm, conjugate), p. 5 (§2.1, ℓ(h(x), y) = L(⟨w, x⟩ − y)), p. 8 (§3.1 preamble, norm on ℝ^{n+1}), p. 30 (proof of Lemma A.3, Θ = {θ ∈ ℝ : L*(θ) < ∞})

import Mathlib
import Definitions.Def_RegMT_Classif_Model

namespace RegMT.Regress

/-- The linear functional `ξ = (x, y) ↦ ⟨w, x⟩ − y` on the input-output space,
Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, *Regularization via Mass Transportation*,
arXiv:1710.10016v3, §2.1 (p. 5) and §3.1 (p. 8): the residual of the linear hypothesis
`h(x) = ⟨w, x⟩` at the pair `(x, y)`, so that the regression loss is `ℓ(⟨w, x⟩, y) = L(pairing e w ξ)`.

The input-output space `ℝ^{n+1}` carries an arbitrary norm (§3.1); it is modelled as an abstract
normed space `E` together with a continuous linear isomorphism `e : E ≃L[ℝ] ℝⁿ × ℝ` that reads off
the input `x = (e ξ).1` and the output `y = (e ξ).2`. As a functional on `E`, `pairing e w` is the
vector `(w, −1)` of the paper, and its operator norm `‖pairing e w‖` is the dual norm
`‖(w, −1)‖_*` of §1.1 (p. 4) for the norm of `E`. -/
noncomputable def pairing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (e : E ≃L[ℝ] (Fin n → ℝ) × ℝ) (w : Fin n → ℝ) : E →L[ℝ] ℝ :=
  ((∑ j, w j • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ)) -
    ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ).comp (e : E →L[ℝ] (Fin n → ℝ) × ℝ)

@[simp] theorem pairing_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (e : E ≃L[ℝ] (Fin n → ℝ) × ℝ) (w : Fin n → ℝ) (ξ : E) :
    pairing e w ξ = ∑ j, w j * (e ξ).1 j - (e ξ).2 := by
  simp [pairing]

end RegMT.Regress



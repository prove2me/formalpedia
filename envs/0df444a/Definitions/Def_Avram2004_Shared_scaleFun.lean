-- Prove2me | Definitions.Def_Avram2004_Shared_scaleFun
-- name    : Avram2004_Shared_scaleFun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:18:24.588412+00:00
-- url     : https://prove2.me/theorems/7333c356-84b5-49a1-836f-9ba767eca48b
-- title:
--   Definitions 1–3: Φ(q), the q-scale function W^(q), its extension (5) to q < 0, and Z^(q)
-- statement:
--   Fix an exponent $\varphi:\mathbb R\to\mathbb R$ (below, $\varphi$ is the Laplace exponent $\psi$ of a spectrally negative Lévy process or one of its tilts $\psi_c$).
--
--   1. **Definition 1.** For $q\ge0$, $\Phi(q)$ is the largest root of $\varphi(\theta)=q$; it is taken as the supremum of $\{\theta\ge0:\varphi(\theta)=q\}$.
--   2. **Definition 2.** For $q\ge0$, the **$q$-scale function** $W^{(q)}:\mathbb R\to[0,\infty)$ is the unique function which is identically zero on $(-\infty,0]$, continuous on $(0,\infty)$, and has Laplace transform
--   $$\int_0^\infty e^{-\theta x}W^{(q)}(x)\,dx=\big(\varphi(\theta)-q\big)^{-1},\qquad \theta>\Phi(q).$$
--   3. **Convolution powers.** For a function $W$ vanishing on $(-\infty,0]$, $W^{\star1}=W$ and $W^{\star(k+2)}(x)=\int_0^xW^{\star(k+1)}(x-y)\,W(y)\,dy$.
--   4. **Extension (5).** For $q<0$ the scale function is defined by the series
--   $$W^{(q)}(x)=\sum_{k\ge0}q^kW^{\star(k+1)}(x),\qquad W=W^{(0)}.$$
--   5. **Definition 3, (6).** For every real $q$,
--   $$Z^{(q)}(x)=1+q\int_{-\infty}^xW^{(q)}(z)\,dz .$$
--
--   The scale functions $W^{(q)}$ and $Z^{(q)}$ are the building blocks of every exit identity of the paper: the two-sided exit problem of Proposition 1 and the reflected exit problem of Theorem 1 are both expressed through them.
--
--   **Formalization Note** $W^{(q)}$ is a definite description: the function chosen among those with the properties of Definition 2 (the paper asserts that there is exactly one), with the constant $0$ as a placeholder that is never reached for a genuine Lévy exponent. For $q\ge0$ Definition 2 is used, for $q<0$ the series (5); the paper extends $q\mapsto W^{(q)}(x)$ to all complex $q$, but only real $q$ occurs in its statements. The integral in (6) is taken over $(-\infty,x]$ literally. The restriction $\theta\ge0$ in Definition 1 does not change the largest root, because $\varphi(0)=0\le q$ and $\varphi(\theta)\to\infty$.
--
--   **Shared definition.** This is the group's single copy of this definition, reviewed once for every chunk that uses it: `01-reflected-exit` (Theorem 1: Eq. (2) p. 216, Remark 4 p. 218, Proposition 1 p. 219, Theorem 1 and its proof pp. 220–224, Remark 6 p. 225); `02-russian` (Theorem 2: Remarks 3–4 and Lemma 1 p. 218, the Russian problem (27)–(28) pp. 227–228, Corollary 1 p. 228, Lemma 2 and Theorem 2 p. 229, proof of Theorem 2 pp. 230–231); `03-canadized-russian` (Theorem 3: Corollary 1 p. 228, Lemma 2 (i) p. 229, the Canadized problem (32) and Lemma 3 pp. 231–233, Theorem 3 p. 233, Lemma 4 p. 234, proof of Theorem 3 pp. 234–235).
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, pp. 217–218, Definition 1, Definition 2, Eq. (5), Definition 3 Eq. (6)

import Mathlib

open MeasureTheory

namespace Avram2004.Shared

/-- Definition 1: `Φ(q)`, the largest root of `φ(θ) = q`, for an exponent `φ` (the Laplace exponent
`ψ` or one of its tilts `ψ_c`). For `q ≥ 0` the largest root is `≥ 0` (as `φ(0) = 0 ≤ q` and
`φ(θ) → ∞`), so restricting to `θ ≥ 0` does not change it. -/
noncomputable def Phi (φ : ℝ → ℝ) (q : ℝ) : ℝ :=
  sSup {θ : ℝ | 0 ≤ θ ∧ φ θ = q}

/-- The defining property of the `q`-scale function of Definition 2 for the exponent `φ`:
`W : ℝ → [0, ∞)`, identically zero on `(-∞, 0]`, continuous on `(0, ∞)`, with Laplace transform
`∫_0^∞ e^{-θx} W(x) dx = (φ(θ) - q)⁻¹` for every `θ > Φ(q)` (the integral converging absolutely). -/
def IsScaleFun (φ : ℝ → ℝ) (q : ℝ) (W : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ W x) ∧ (∀ x ≤ 0, W x = 0) ∧ ContinuousOn W (Set.Ioi 0) ∧
    ∀ θ > Phi φ q, IntegrableOn (fun x => Real.exp (-θ * x) * W x) (Set.Ioi 0) ∧
      ∫ x in Set.Ioi 0, Real.exp (-θ * x) * W x = (φ θ - q)⁻¹

/-- Definition 2: the `q`-scale function `W^{(q)}` of the exponent `φ`, i.e. the unique function with
the properties of `IsScaleFun` (the paper asserts existence and uniqueness; the constant `0` is only
a placeholder for the case where no such function exists). -/
noncomputable def scaleFun (φ : ℝ → ℝ) (q : ℝ) : ℝ → ℝ :=
  open Classical in if h : ∃ W, IsScaleFun φ q W then h.choose else 0

/-- Convolution powers on `[0, ∞)`: `convPow W k` is the `(k+1)`-th convolution power `W^{⋆(k+1)}`,
with `W^{⋆1} = W` and `W^{⋆(k+2)}(x) = ∫_0^x W^{⋆(k+1)}(x - y) W(y) dy`. -/
noncomputable def convPow (W : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => W
  | k + 1 => fun x => ∫ y in (0 : ℝ)..x, convPow W k (x - y) * W y

/-- The scale function `W^{(q)}` for every real `q`: Definition 2 when `q ≥ 0`, and the paper's
extension (5), `W^{(q)}(x) = ∑_{k ≥ 0} q^k W^{⋆(k+1)}(x)` with `W = W^{(0)}`, when `q < 0`. -/
noncomputable def scaleFunExt (φ : ℝ → ℝ) (q : ℝ) : ℝ → ℝ :=
  fun x => if 0 ≤ q then scaleFun φ q x
    else ∑' k : ℕ, q ^ k * convPow (scaleFun φ 0) k x

/-- Definition 3, (6): `Z^{(q)}(x) = 1 + q ∫_{-∞}^x W^{(q)}(z) dz`, for every real `q`
(with the extended `W^{(q)}` when `q < 0`). -/
noncomputable def scaleZ (φ : ℝ → ℝ) (q : ℝ) : ℝ → ℝ :=
  fun x => 1 + q * ∫ z in Set.Iic x, scaleFunExt φ q z

end Avram2004.Shared



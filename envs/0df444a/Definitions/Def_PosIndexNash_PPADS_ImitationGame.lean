-- Prove2me | Definitions.Def_PosIndexNash_PPADS_ImitationGame
-- name    : PosIndexNash_PPADS_ImitationGame
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:32:13.886111+00:00
-- url     : https://prove2.me/theorems/f1696a5e-dccd-403d-9a07-2bcac21f2bbe
-- title:
--   The symmetric game S, the strategies y(x) and u(x), the shifted matrix R and the perturbed games G(t) (§6, (45)–(58))
-- statement:
--   Let $M, b$ come from an anchored normal form with $m$ gates, and let $N = m + 1$ with an extra strategy $\star$ placed last. The **symmetric game** matrix is
--   $$S := \begin{pmatrix} -M & b + \mathbf 1 \\ \mathbf 0^\top & 1\end{pmatrix} \in \mathbb{Q}^{N\times N}. \tag{45}$$
--   For $x \in \mathbb{R}^m$ put $y(x) := (x, 1)/(1 + \mathbf 1^\top x)$ (46), $I(x) := \{i : x_i > 0\}$, $K := I(x) \cup \{\star\}$, and let $u(x)$ be the uniform distribution on $K$ (50). The **imitation game** is $(S, I_N)$ (49).
--
--   For an integer $c$, $R := S + c\,\mathbf 1\mathbf 1^\top$ (57). For $0 \le t < 1$ let $\alpha_i(t) := 1 + t^i$ ($i \in [N]$), $D(t) := \mathrm{diag}(\alpha(t))$, $R(t) := D(t)^{-1}R$ and $G(t) := (R(t), I_N)$ (58); so $G(0) = (R, I_N)$.
--
--   **Formalization Note** Strategy $i \in [m]$ is `Fin.castSucc i` and $\star$ is `Fin.last m` (0-based), so $\alpha$ of the 0-based strategy $i$ is $1 + t^{i+1}$. `symGameS`, `yOf`, `Kset`, `uOf`, `shiftR`, `alphaW`, `perturbedR` and `perturbedGame` (a public `QuasiStrictNE.RatGame`) are the objects above.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), pp. 40–44, (45), (46), (49), (50), (57), (58)

import Mathlib
import Definitions.Def_QuasiStrictNE_supp
import Definitions.Def_QuasiStrictNE_RatGame
import Definitions.Def_PosIndexNash_PPADS_NormalForm

namespace PosIndexNash.PPADS

open Matrix

/-- **The symmetric game matrix `S`** (Kontogiannis, Panageas, Pollatos, Yan, *Finding a Positive
Index Nash Equilibrium is PPADS-Complete*, arXiv:2609.23879, §6.1, p. 40, (45)):
`S := (−M, b + 1; 0ᵀ, 1) ∈ ℚ^{N×N}`, `N = m + 1`, with the extra strategy `⋆` last.

**Formalization Note** `M` and `b` are those of the normal form `F` (§5, (36), (39)); the strategy
`⋆` is the index `Fin.last m`, and strategy `i ∈ [m]` is `Fin.castSucc i` (0-based). -/
def symGameS (F : NormalForm) : Matrix (Fin (F.m + 1)) (Fin (F.m + 1)) ℚ :=
  Matrix.of fun i j =>
    Fin.lastCases (Fin.lastCases (1 : ℚ) (fun _ => 0) j)
      (fun i' => Fin.lastCases (F.b i' + 1) (fun j' => -F.M i' j') j) i

/-- **The column strategy `y(x) := (x, 1)/(1 + 1ᵀx)`** (p. 41, (46); p. 42, (50)) attached to an
LCP vector `x ∈ ℝ^m`. -/
noncomputable def yOf {m : ℕ} (x : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  fun i => Fin.lastCases (1 : ℝ) (fun i' => x i') i / (1 + ∑ j, x j)

/-- **The support `K = I(x) ∪ {⋆}`** (p. 42), `I(x) := {i ∈ [m] : x_i > 0}`, as a set of
strategies of `[N]`. -/
noncomputable def Kset {m : ℕ} (x : Fin m → ℝ) : Finset (Fin (m + 1)) :=
  (QuasiStrictNE.supp x).map (Fin.castSuccEmb) ∪ {Fin.last m}

/-- **The row strategy `u(x)`** (p. 42, (50)): uniform on `K = I(x) ∪ {⋆}`,
`u_i = 1/|K|` for `i ∈ K` and `u_i = 0` otherwise. -/
noncomputable def uOf {m : ℕ} (x : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  fun i => if i ∈ Kset x then 1 / ((Kset x).card : ℝ) else 0

/-- **The shifted row matrix `R := S + c 1 1ᵀ`** (p. 44, (57)) for an integer `c`. -/
def shiftR (F : NormalForm) (c : ℤ) : Matrix (Fin (F.m + 1)) (Fin (F.m + 1)) ℚ :=
  symGameS F + Matrix.of fun _ _ => (c : ℚ)

/-- **The perturbation weights** `α_i(t) := 1 + t^i`, `i ∈ [N]` (p. 44).

**Formalization Note** Strategy `i` is 0-based here, so the weight of `i : Fin N` is
`1 + t^{i+1}`. -/
def alphaW {N : ℕ} (t : ℚ) (i : Fin N) : ℚ := 1 + t ^ (i.val + 1)

/-- **The perturbed row matrix `R(t) := D(t)^{−1} R`** (p. 44, (58)),
`D(t) = diag(α_1(t), …, α_N(t))`: row `i` of `R` divided by `α_i(t)`. -/
def perturbedR (F : NormalForm) (c : ℤ) (t : ℚ) : Matrix (Fin (F.m + 1)) (Fin (F.m + 1)) ℚ :=
  Matrix.of fun i j => shiftR F c i j / alphaW t i

/-- **The perturbed game `G(t) := (R(t), C)`, `C := I_N`** (p. 44, (57)–(58)), as a rational
bimatrix game. `G(0) = (R, I_N)`. -/
def perturbedGame (F : NormalForm) (c : ℤ) (t : ℚ) : QuasiStrictNE.RatGame :=
  ⟨F.m + 1, F.m + 1, perturbedR F c t, (1 : Matrix (Fin (F.m + 1)) (Fin (F.m + 1)) ℚ)⟩

end PosIndexNash.PPADS



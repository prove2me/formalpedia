-- Prove2me | Definitions.Def_GUT_standard_model_group
-- name    : GUT_standard_model_group
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T00:32:27.94297+00:00
-- url     : https://prove2.me/theorems/08e6d5d0-fb47-48fb-8707-85c1df737390
-- title:
--   The gauge groups $G_{\mathrm{SM}}$, $\mathrm{SU}(5)$, and the maps $\varphi$, $\beta$
-- statement:
--   This file fixes the groups and the two homomorphisms out of the Standard Model gauge group that the mission is about.
--
--   The **Standard Model gauge group** is the compact Lie group
--
--   $$G_{\mathrm{SM}} \;=\; \mathrm{U}(1)\times\mathrm{SU}(2)\times\mathrm{SU}(3),$$
--
--   with $\mathrm{U}(1)$ the complex numbers of modulus one and $\mathrm{SU}(n)$ the unitary $n\times n$ complex matrices of determinant one. A typical element is written $x = (\alpha, g, h)$.
--
--   Two index sets encode the splittings that the grand unified theories use. $\mathbb{C}^5$ is indexed by $\{0,1\}\sqcup\{0,1,2\}$, which records the splitting $\mathbb{C}^5\cong\mathbb{C}^2\oplus\mathbb{C}^3$ into the weak-isospin and colour parts; $\mathbb{C}^4$ is indexed by $\{0,1,2\}\sqcup\{0\}$, recording $\mathbb{C}^4\cong\mathbb{C}^3\oplus\mathbb{C}$, "colour plus lepton number as a fourth colour".
--
--   The **Georgi-Glashow map** sends $x = (\alpha,g,h)$ to the $5\times5$ block matrix
--
--   $$\varphi(x) \;=\; \begin{pmatrix}\alpha^{3}g & 0\\ 0 & \alpha^{-2}h\end{pmatrix},$$
--
--   and the **Pati-Salam map** sends $x$ to the triple
--
--   $$\beta(x) \;=\; \left(g,\;\begin{pmatrix}\alpha^{3}&0\\0&\alpha^{-3}\end{pmatrix},\;\begin{pmatrix}\alpha h&0\\0&\alpha^{-3}\end{pmatrix}\right).$$
--
--   The exponents are exactly those of the source: they are forced by requiring the image to have determinant one, and by matching the hypercharges of the quarks and leptons.
--
--   Both maps are introduced here as plain matrix-valued functions. That they take values in $\mathrm{SU}(5)$, respectively $\mathrm{SU}(2)\times\mathrm{SU}(2)\times\mathrm{SU}(4)$, and that they are group homomorphisms, are stated as separate theorems of the mission rather than built into the definitions.
-- source:
--   John Baez and John Huerta, The Algebra of Grand Unified Theories, https://math.ucr.edu/home/baez/guts.pdf, Section 3.1 p. 34 (the map φ) and Section 3.3 p. 54 (the map β)

import Mathlib

namespace GrandUnifiedTheories

open Matrix

/-- Index type for `ℂ⁵ ≅ ℂ² ⊕ ℂ³`, the 2+3 splitting used by the SU(5) theory. -/
abbrev Idx5 : Type := Fin 2 ⊕ Fin 3

/-- Index type for `ℂ⁴ ≅ ℂ³ ⊕ ℂ`, the colour + lepton splitting of the Pati-Salam model. -/
abbrev Idx4 : Type := Fin 3 ⊕ Fin 1

/-- The Standard Model gauge group `G_SM = U(1) × SU(2) × SU(3)`. -/
abbrev GSM : Type :=
  Circle × Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 3) ℂ

/-- The matrix underlying the Georgi-Glashow homomorphism `φ : G_SM → SU(5)`,
`(α, g, h) ↦ diag(α³g, α⁻²h)` written in the 2+3 block decomposition of `ℂ⁵`. -/
noncomputable def phiMatrix (x : GSM) : Matrix Idx5 Idx5 ℂ :=
  Matrix.fromBlocks
    (((x.1 : ℂ) ^ 3) • (x.2.1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0
    ((((x.1)⁻¹ : Circle) : ℂ) ^ 2 • (x.2.2 : Matrix (Fin 3) (Fin 3) ℂ))

/-- The matrices underlying the Pati-Salam homomorphism
`β : G_SM → SU(2) × SU(2) × SU(4)`, `(α, g, h) ↦ (g, diag(α³, α⁻³), diag(αh, α⁻³))`. -/
noncomputable def betaMatrix (x : GSM) :
    Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ × Matrix Idx4 Idx4 ℂ :=
  ((x.2.1 : Matrix (Fin 2) (Fin 2) ℂ),
    Matrix.diagonal ![(x.1 : ℂ) ^ 3, (((x.1)⁻¹ : Circle) : ℂ) ^ 3],
    Matrix.fromBlocks ((x.1 : ℂ) • (x.2.2 : Matrix (Fin 3) (Fin 3) ℂ)) 0 0
      (Matrix.diagonal fun _ => (((x.1)⁻¹ : Circle) : ℂ) ^ 3))

end GrandUnifiedTheories



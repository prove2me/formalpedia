-- Prove2me | Definitions.Def_FiniteEnergyPlane_GraphEnd
-- name    : FiniteEnergyPlane_GraphEnd
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-11-20T11:25:28.872555+00:00
-- url     : https://prove2.me/theorems/19dd0de4-c0bb-4c14-a1d0-5efc7f484d71
-- title:
--   Normal coordinates of a map relative to a graph along a cylindrical end
-- statement:
--   Fix a real-linear structure field $\bar J : \mathbb{C} \times \mathbb{C} \to \mathrm{End}_{\mathbb{R}}(\mathbb{C} \times \mathbb{C})$, a function $g : \mathbb{C} \to \mathbb{C}$ (its graph $x \mapsto (x, g(x))$ is the reference surface), the two components $\psi, v : \mathbb{C} \to \mathbb{C}$ of a map $z \mapsto (\psi(z), v(z))$, and a bump function $\beta$ around $0 \in \mathbb{C}$ (`ContDiffBump`).
--
--   **Blocks.** For $J \in \mathrm{End}_{\mathbb{R}}(\mathbb{C} \times \mathbb{C})$, `J11 J`, `J12 J`, `J21 J`, `J22 J` are its four $\mathbb{C} \to \mathbb{C}$ blocks. For $G \in \mathrm{End}_{\mathbb{R}}(\mathbb{C})$,
--   $$\texttt{Ablk}\,J\,G = J_{21} - G J_{11} + J_{22} G - G J_{12} G, \qquad \texttt{Bblk}\,J\,G = J_{22} - G J_{12},$$
--   the lower blocks of $J$ written in the frame adapted to a graph with derivative $G$.
--
--   **Frames of $\mathbb{C}$.** `qinvL c` is $a + ib \mapsto a + b\,c$, and `qL c` is $a + ib \mapsto a + b\,(i - \operatorname{Re} c)/\operatorname{Im} c$ (the inverse of `qinvL c` when $\operatorname{Im} c \neq 0$).
--
--   **Re-centred structure.** `rtr β w` $= \beta(w)\,w$; `Jt Jbar β (x, w)` $= \bar J(x, \beta(w) w)$;
--   `Afun Jbar β g (x, η)` and `Bfun Jbar β g (x, η)` are `Ablk` and `Bblk` of `Jt` at $(x, g(x) + \eta)$ with $G = Dg(x)$;
--   `KA`, `KB` at $(x, \eta)$ are $\int_0^1 \partial_\eta \mathrm{Afun}(x, \theta\eta)\,d\theta$ and $\int_0^1 \partial_\eta \mathrm{Bfun}(x, \theta\eta)\,d\theta$; and `C0 Jbar β g x` $=$ `Bfun` $(x, 0)$, the normal structure along the graph.
--
--   **Along the map.** `cc z` $= C_0(\psi(z))\,1$, the frame `Pf z` $=$ `qL (cc z)`, the difference `hd z` $= v(z) - g(\psi(z))$, and the operator
--   $$\texttt{Lmap}\,z\,e = DP_z(ie) - i\,DP_z(e) + P_z \circ \big(K_A(\psi z, h z)(\cdot)(D\psi_z e)\big) + P_z \circ \big(K_B(\psi z, h z)(\cdot)(Dh_z e)\big),$$
--   with $P = $ `Pf`, $h = $ `hd`.
--
--   **Matrices.** `reIm`, `basisC` are the real coordinates and the basis $1, i$ of $\mathbb{C}$ indexed by `Fin 1 ⊕ Fin 1`, and `cMat T` is the real $2 \times 2$ matrix (`CauchyRiemannIndex.Mat 1`) of $T \in \mathrm{End}_{\mathbb{R}}(\mathbb{C})$ in that basis.
--
--   **On the cylindrical end.** With $z = $ `cylInf s t` $= e^{2\pi(s + it)}$: the normal coordinate `ζf z` $= P_z(v(z) - g(\psi(z)))$; `c2 (s, t)` $= 2\pi\,z$; the coefficient `Tf (s, t)` $= -i \cdot \texttt{Lmap}(z, 2\pi z) \circ \texttt{qinvL}(\texttt{cc}\,z)$; its matrix `Sf (s, t) = cMat (Tf (s, t))`; and the vector `wf (s, t) = cToVec (ζf z)` $\in \mathbb{R}^2$.
--
--   Role: the common vocabulary for statements about the difference between a holomorphic map and a complex graph inside a standard tube, written in frame-normalised coordinates on the cylindrical end.
-- source:
--   Standard tube structures in the theory of fast finite-energy planes; U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6

import Definitions.Def_FiniteEnergyPlane_Tube
import Definitions.Def_FiniteEnergyPlane_TubeFamily

/-!
# Normal coordinates of a holomorphic map relative to a graph, along a cylindrical end

Let `Jbar` be a real-linear structure field on `ℂ × ℂ`, `g : ℂ → ℂ` a function whose graph is the
reference surface, `ψ, v : ℂ → ℂ` the two components of a map `z ↦ (ψ z, v z)`, and `β` a bump
function around `0 ∈ ℂ`. This file defines:

* the blocks `J11, J12, J21, J22` of a real-linear map of `ℂ × ℂ`, and the blocks `Ablk J G`,
  `Bblk J G` of `J` re-centred at a graph with derivative `G`;
* the real-linear maps `qinvL c : a + ib ↦ a + b c` and `qL c` (its inverse when `c.im ≠ 0`);
* the retraction `rtr β w = β(w) w`, the retracted structure `Jt`, the re-centred blocks
  `Afun`, `Bfun` at `(x, g x + η)`, their averaged `η`-derivatives `KA`, `KB` along `[0, 1]`, and
  the normal structure `C0 x = Bfun (x, 0)`;
* `cc z = C0 (ψ z) 1`, the frame `Pf z = qL (cc z)`, the difference `hd z = v z - g (ψ z)` and the
  defect operator `Lmap z e`;
* on the cylinder `(s, t) ↦ cylInf s t`: the normal coordinate `ζf z = Pf z (hd z)`, the coefficient
  `Tf (s, t)` (a real-linear map of `ℂ`), its `2 × 2` matrix `Sf (s, t) = cMat (Tf (s, t))`, and
  the vector `wf (s, t) = cToVec (ζf (cylInf s t))`.
-/

namespace FiniteEnergyPlane.GraphEnd

open MeasureTheory ContinuousLinearMap CauchyRiemannIndex
open scoped Real

noncomputable section

/-! ### Blocks of a real-linear map of `ℂ × ℂ` -/

/-- Upper-left block. -/
def J11 (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) : ℂ →L[ℝ] ℂ := (fst ℝ ℂ ℂ).comp (J.comp (inl ℝ ℂ ℂ))
/-- Upper-right block. -/
def J12 (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) : ℂ →L[ℝ] ℂ := (fst ℝ ℂ ℂ).comp (J.comp (inr ℝ ℂ ℂ))
/-- Lower-left block. -/
def J21 (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) : ℂ →L[ℝ] ℂ := (snd ℝ ℂ ℂ).comp (J.comp (inl ℝ ℂ ℂ))
/-- Lower-right block. -/
def J22 (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) : ℂ →L[ℝ] ℂ := (snd ℝ ℂ ℂ).comp (J.comp (inr ℝ ℂ ℂ))

/-- Lower-left block of `J` re-centred at a graph with derivative `G`. -/
def Ablk (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) (G : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ :=
  J21 J - G.comp (J11 J) + (J22 J).comp G - G.comp ((J12 J).comp G)

/-- Lower-right block of `J` re-centred at a graph with derivative `G`. -/
def Bblk (J : ℂ × ℂ →L[ℝ] ℂ × ℂ) (G : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ := J22 J - G.comp (J12 J)

/-! ### Frames of `ℂ` -/

/-- `a + ib ↦ a + b c`. -/
def qinvL (c : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight (1 : ℂ) + Complex.imCLM.smulRight c

/-- `a + ib ↦ a + b (i - Re c) / Im c`, the inverse of `qinvL c` when `c.im ≠ 0`. -/
def qL (c : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight (1 : ℂ) + Complex.imCLM.smulRight ((Complex.I - c.re) / c.im)

/-! ### The re-centred structure -/

/-- The retraction `w ↦ β(w) w`. -/
def rtr (β : ContDiffBump (0 : ℂ)) (w : ℂ) : ℂ := β w • w

variable (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (β : ContDiffBump (0 : ℂ)) (g : ℂ → ℂ)

/-- The retracted structure. -/
def Jt (p : ℂ × ℂ) : ℂ × ℂ →L[ℝ] ℂ × ℂ := Jbar (p.1, rtr β p.2)

/-- Lower-left block of the structure re-centred at the graph of `g`, at `(x, g x + η)`. -/
def Afun (p : ℂ × ℂ) : ℂ →L[ℝ] ℂ := Ablk (Jt Jbar β (p.1, g p.1 + p.2)) (fderiv ℝ g p.1)

/-- Lower-right block of the re-centred structure. -/
def Bfun (p : ℂ × ℂ) : ℂ →L[ℝ] ℂ := Bblk (Jt Jbar β (p.1, g p.1 + p.2)) (fderiv ℝ g p.1)

/-- `η`-derivative of `Afun` averaged along the segment `[0, p.2]`. -/
def KA (p : ℂ × ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  ∫ θ in (0 : ℝ)..1, fderiv ℝ (fun a => Afun Jbar β g (p.1, a)) (θ • p.2)

/-- `η`-derivative of `Bfun` averaged along the segment `[0, p.2]`. -/
def KB (p : ℂ × ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  ∫ θ in (0 : ℝ)..1, fderiv ℝ (fun a => Bfun Jbar β g (p.1, a)) (θ • p.2)

/-- The normal structure along the graph. -/
def C0 (x : ℂ) : ℂ →L[ℝ] ℂ := Bfun Jbar β g (x, 0)

variable (ψ v : ℂ → ℂ)

/-- `C0 (ψ z) 1`. -/
def cc (z : ℂ) : ℂ := C0 Jbar β g (ψ z) 1

/-- The frame. -/
def Pf (z : ℂ) : ℂ →L[ℝ] ℂ := qL (cc Jbar β g ψ z)

/-- The difference of `v` and the graph of `g` over `ψ`. -/
def hd (z : ℂ) : ℂ := v z - g (ψ z)

/-- The defect operator. -/
def Lmap (z e : ℂ) : ℂ →L[ℝ] ℂ :=
  fderiv ℝ (Pf Jbar β g ψ) z (Complex.I * e) - Complex.I • fderiv ℝ (Pf Jbar β g ψ) z e +
    (Pf Jbar β g ψ z).comp ((ContinuousLinearMap.apply ℝ ℂ (fderiv ℝ ψ z e)).comp
      (KA Jbar β g (ψ z, hd g ψ v z))) +
    (Pf Jbar β g ψ z).comp ((ContinuousLinearMap.apply ℝ ℂ (fderiv ℝ (hd g ψ v) z e)).comp
      (KB Jbar β g (ψ z, hd g ψ v z)))

/-! ### Matrices -/

/-- Real and imaginary part, indexed by `Fin 1 ⊕ Fin 1`. -/
def reIm : Fin 1 ⊕ Fin 1 → ℂ → ℝ := Sum.elim (fun _ (y : ℂ) => y.re) (fun _ (y : ℂ) => y.im)

/-- The real basis `1, i` of `ℂ`. -/
def basisC : Fin 1 ⊕ Fin 1 → ℂ := Sum.elim (fun _ => (1 : ℂ)) (fun _ => Complex.I)

/-- The real `2 × 2` matrix of a real-linear map `ℂ → ℂ`. -/
def cMat (T : ℂ →L[ℝ] ℂ) : Mat 1 := Matrix.of fun i j => reIm i (T (basisC j))

/-! ### Along the cylindrical end -/

/-- The normal coordinate `ζ(z) = P(z)(v z - g (ψ z))`. -/
def ζf (z : ℂ) : ℂ := Pf Jbar β g ψ z (v z - g (ψ z))

/-- `2π · cylInf s t`. -/
def c2 (p : ℝ × ℝ) : ℂ := ((2 * π : ℝ) : ℂ) * cylInf p.1 p.2

/-- The coefficient on the cylinder, as a real-linear map of `ℂ`. -/
def Tf (p : ℝ × ℝ) : ℂ →L[ℝ] ℂ :=
  (-Complex.I) • ((Lmap Jbar β g ψ v (cylInf p.1 p.2) (c2 p)).comp
    (qinvL (cc Jbar β g ψ (cylInf p.1 p.2))))

/-- The coefficient matrix on the cylinder. -/
def Sf (p : ℝ × ℝ) : Mat 1 := cMat (Tf Jbar β g ψ v p)

/-- The normal coordinate on the cylinder. -/
def wf (p : ℝ × ℝ) : Vec 1 := cToVec (ζf Jbar β g ψ v (cylInf p.1 p.2))

end

end FiniteEnergyPlane.GraphEnd



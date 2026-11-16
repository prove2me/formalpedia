-- Prove2me | Definitions.Def_PathRecording_Supplement_DualData
-- name    : PathRecording_Supplement_DualData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:29:29.800897+00:00
-- url     : https://prove2.me/theorems/a3114c6a-aba6-4904-9e9b-19fddabbc578
-- title:
--   Dual labels $\lambda^*$, the identification $V_{\lambda^*}\cong V_\lambda^*$, and the maps $K$, $\mathrm{Sw}$, $D_J$ on $\mathrm{Tab}(\widehat G)$
-- statement:
--   Let $\widehat G$ be the complete catalogue of irreducible representations of $G$. **Dual-label data** assign to each label $\lambda$ a label $\lambda^*$ and a unitary matrix $J_\lambda$ identifying the dual basis of $V_\lambda^*$ with the basis of $V_{\lambda^*}$, in the sense that
--   $$\overline{\rho_\lambda(g)}=J_\lambda\,\rho_{\lambda^*}(g)\,J_\lambda^\dagger\qquad\text{for all }g\in G,$$
--   where the bar is the entrywise complex conjugate. On the tableau space with basis $|\lambda,X,Y\rangle$ the following maps are defined:
--   1. $K$, the complex conjugation of all coordinates; for an operator $T$, $\overline T=KTK$;
--   2. $\mathrm{Sw}:|\lambda,X,Y\rangle\mapsto|\lambda,Y,X\rangle$;
--   3. $D_J:|\lambda,X,Y\rangle\mapsto\sum_{X',Y'}\overline{(J_\lambda)_{XX'}}\,(J_\lambda)_{YY'}\,|\lambda^*,X',Y'\rangle$, and $\overline{D_J}=KD_JK$, the same map with conjugated coefficients.
--
--   When $J_\lambda=I$ (the paper's choice of bases, where $\rho_{\lambda^*}(g)=\rho_\lambda(g)^*$), $D_J$ is the relabelling $|\lambda,X,Y\rangle\mapsto|\lambda^*,X,Y\rangle$. These maps are the pre- and post-processing that turn a forward tableau oracle into conjugate, transpose and inverse oracles.
--
--   **Formalization Note** The identification $J_\lambda$ is data, not the identity: $J_\lambda=I$ is impossible for a self-dual irrep of quaternionic type (the defining representation of $SU(2)$). The coefficient of $|\lambda',X',Y'\rangle$ in $D_J w$ is a series over the labels $\lambda$ with $\lambda^*=\lambda'$, which has at most one term.
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, §3.3.1, p.33; p.38 (dual labels); §4.2.2, pp.51–52; p.9 and footnote 9

import Mathlib
import Definitions.Def_PathRecording_Supplement_GHat

set_option autoImplicit false

namespace PathRecording.Supplement

/-!
# Dual labels `λ*`, the identification `V_{λ*} ≅ V_λ*`, and the relabelling maps on `Tab(Ĝ)`

Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, §3.3.1, p.33: "`λ*` denotes a dual representation acting as `ρ_{λ*}(g) = ρ_λ(g)*`
on an appropriate dual basis, and we have identified `|X⟩` non-canonically as a basis element of
`V_{λ*}`"; p.38: "for every `λ`, there is a 'dual label' `λ*` such that `V^{λ*}_G ≃ (V^λ_G)*`";
§4.2.2, pp.51–52 (the maps `|λ,X,Y⟩ ↦ |λ*,X,Y⟩`, `|λ,Y,X⟩`, `|λ*,Y,X⟩`); p.9, footnote 9 (the
complex conjugate of `Q^{Tab}_ρ`).

**Formalization Note.**
* The identification of `V_{λ*}` with `V_λ*` is data: a unitary `J_λ` with
  `\overline{ρ_λ(g)} = J_λ ρ_{λ*}(g) J_λ†` for all `g` (entrywise conjugate). The paper's choice is
  `J_λ = I`; that choice is impossible for a self-dual irrep of quaternionic type (the defining irrep
  of `SU(2)`), so every `J` is allowed.
* All maps act on coefficient functions `w : TabIdx Ĝ → ℂ` of `Tab(Ĝ)` (basis `|λ, X, Y⟩`):
  - `conjTab` is the coordinatewise complex conjugation `K`; for an operator `T`, `K T K` is its
    complex conjugate `\overline{T}` in the basis `|x⟩ ⊗ |λ, X, Y⟩`;
  - `swapTab` is `Sw : |λ, X, Y⟩ ↦ |λ, Y, X⟩`;
  - `dualMap D` is `D_J : |λ, X, Y⟩ ↦ Σ_{X', Y'} \overline{(J_λ)_{X X'}} (J_λ)_{Y Y'} |λ*, X', Y'⟩`
    (`|λ, X, Y⟩ ↦ |λ*, X, Y⟩` when `J = I`), and `conjDualMap D = K D_J K` is the same map with
    conjugated coefficients. The coefficient of `|λ', X', Y'⟩` in `D_J w` is a sum over the labels
    `λ` with `λ* = λ'` (at most one: distinct labels are inequivalent), written as a `tsum`.
-/

open Matrix

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Dual-label data for `Ĝ`: for each label `λ` a label `λ*` and a unitary `J_λ : V_{λ*} → V_λ` with
`\overline{ρ_λ(g)} = J_λ ρ_{λ*}(g) J_λ†` (arXiv:2606.30281v2, pp.33, 38). -/
structure DualData (Ĝ : GHat.{u, v} G) where
  /-- The dual label `λ ↦ λ*`. -/
  dual : Ĝ.Charge → Ĝ.Charge
  /-- The identification `J_λ` of the dual basis of `V_λ*` with the basis of `V_{λ*}`. -/
  J : (a : Ĝ.Charge) → Matrix (Fin (Ĝ.dim a)) (Fin (Ĝ.dim (dual a))) ℂ
  /-- `J_λ J_λ† = I`. -/
  J_mul_conjTranspose : ∀ a, J a * (J a)ᴴ = 1
  /-- `J_λ† J_λ = I`. -/
  conjTranspose_mul_J : ∀ a, (J a)ᴴ * J a = 1
  /-- `\overline{ρ_λ(g)} = J_λ ρ_{λ*}(g) J_λ†`. -/
  conj_rep : ∀ a (g : G), ((Ĝ.urep a).mat g).map star = J a * (Ĝ.urep (dual a)).mat g * (J a)ᴴ

variable {Ĝ : GHat.{u, v} G}

/-- Coordinatewise complex conjugation `K` on `Tab(Ĝ)`. -/
def conjTab (w : Ĝ.TabIdx → ℂ) : Ĝ.TabIdx → ℂ := fun b => star (w b)

/-- The swap `Sw : |λ, X, Y⟩ ↦ |λ, Y, X⟩` on `Tab(Ĝ)` (arXiv:2606.30281v2, p.51). -/
def swapTab (w : Ĝ.TabIdx → ℂ) : Ĝ.TabIdx → ℂ := fun b => w ⟨b.1, (b.2.2, b.2.1)⟩

/-- The kernel of `D_J`: the coefficient of `|λ', X', Y'⟩` in `D_J|λ, X, Y⟩`, namely
`\overline{(J_λ)_{X X'}} (J_λ)_{Y Y'}` if `λ' = λ*`, else `0`. -/
def dualKernel (D : DualData Ĝ) (b b' : Ĝ.TabIdx) : ℂ :=
  if h : D.dual b.1 = b'.1 then
    star (D.J b.1 b.2.1 (Fin.cast (congrArg Ĝ.dim h).symm b'.2.1)) *
      D.J b.1 b.2.2 (Fin.cast (congrArg Ĝ.dim h).symm b'.2.2)
  else 0

/-- `D_J : |λ, X, Y⟩ ↦ Σ_{X', Y'} \overline{(J_λ)_{X X'}} (J_λ)_{Y Y'} |λ*, X', Y'⟩`, the relabelling
between an irrep and its dual (arXiv:2606.30281v2, pp.9, 51–52). -/
noncomputable def dualMap (D : DualData Ĝ) (w : Ĝ.TabIdx → ℂ) : Ĝ.TabIdx → ℂ :=
  fun b' => ∑' b, w b * dualKernel D b b'

/-- `\overline{D_J} = K D_J K`: `D_J` with complex-conjugated coefficients. -/
noncomputable def conjDualMap (D : DualData Ĝ) (w : Ĝ.TabIdx → ℂ) : Ĝ.TabIdx → ℂ :=
  fun b' => ∑' b, w b * star (dualKernel D b b')

end PathRecording.Supplement



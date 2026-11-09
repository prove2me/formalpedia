-- Prove2me | Definitions.Def_GoodQLTC_BaseCodeData
-- name    : GoodQLTC_BaseCodeData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:46:52.254237+00:00
-- url     : https://prove2.me/theorems/a9fcf4a6-fe24-41da-81d7-c03d60a4711e
-- title:
--   Base-code data and compatibility with a cosheaf (Definition 4.8)
-- statement:
--   Fix integers $0<m_{i,b}<n_i$. For each face $f$ choose a vertex $x_f\le f$, put $J_f=\mathrm{codir}(f)$, $U_{f,i}=F^{m_{i,\phi_i(f)}}$, $\Omega_{f,i}=E_i(x_f)$, injective linear maps $G_{f,i}:U_{f,i}\to F^{\Omega_{f,i}}$ with images $C_{f,i}$ (the **local codes**), and isomorphisms $\Psi_{f,g}:\mathcal F(g)\to\bigotimes_{i\in\mathrm{codir}(g)}U_{f,i}$ for $f\le g$. The data is **compatible** with $\mathcal F$ if for every $f$, $T\subseteq J_f$, $\omega\in\Omega_{f,T}$, $j\in J_f\setminus T$, $\omega_j\in\Omega_{f,j}$, the faces $g=\theta_{f,x_f}(T,\omega)$ and $h=\theta_{f,x_f}(T\cup\{j\},(\omega,\omega_j))$ satisfy
--   $$
--   \Psi_{f,h}R_{hg}\Psi_{f,g}^{-1}=(\mathrm{ev}_{\omega_j}\circ G_{f,j})\otimes\bigotimes_{i\in J_f\setminus(T\cup\{j\})}\mathrm{id}_{U_{f,i}} .\tag{4.4}
--   $$
--
--   **Formalization Note** $\theta_{f,x}(T,e)$ is the unique face of type $\mathrm{dir}(f)\cup T$ containing $f$ and every $e_i$ (Lemma 4.3); (4.4) is imposed on every pair $g\le h$ with these defining properties. Tensors are functions on $\prod_{i\in\mathrm{codir}(g)}[m_{i,\phi_i(f)}]$.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §4.3 and Definition 4.8, Equation (4.4), p.17 (PDF p.20); θ from Lemma 4.3, p.15

import Mathlib
import Definitions.Def_GoodQLTC_dir
import Definitions.Def_GoodQLTC_IsRegular
import Definitions.Def_GoodQLTC_Cosheaf

namespace GoodQLTC

/-- The index set of the tensor product `⨂_{i ∈ codir(g)} U_{f,i}`, `U_{f,i} := F^{m_{i,ϕ_i(f)}}`
(arXiv:2609.20780, §4.3, p.17): a tensor is a function on `∏_{i ∈ codir(g)} [m_{i,ϕ_i(f)}]`. -/
abbrev TensorIdx {X : Type} {t : ℕ} (φ : X → Fin t → Option Bool) (m : Fin t → Bool → ℕ)
    (f g : X) : Type :=
  ∀ i : {i // i ∈ codir φ g}, Fin (m i.1 (bit φ f i.1))

/-- The **base-code data** of §4.3, Gay–Jeronimo, arXiv:2609.20780 (held version), p.17, for a
cosheaf `F` on `X` and integers `m_{i,b}`: for each face `f` a vertex `x_f ≤ f`; for `i ∈ J_f :=
codir(f)` an injective linear map `G_{f,i} : U_{f,i} := F^{m_{i,ϕ_i(f)}} → F^{Ω_{f,i}}`,
`Ω_{f,i} := E_i(x_f)`; and for each `f ≤ g` an isomorphism
`Ψ_{f,g} : F(g) → ⨂_{i∈codir(g)} U_{f,i}`.

**Formalization Note.** `G f i` is the matrix of `G_{f,i}` (rows indexed by `E_i(x_f)`); it is
required injective only for `i ∈ codir(f)`, and its value for `i ∉ codir(f)` is never used.
`m i false = m_{i,0}`, `m i true = m_{i,1}`. Tensors are functions on `TensorIdx`. -/
structure BaseCodeData {X : Type} [PartialOrder X] {t : ℕ} (φ : X → Fin t → Option Bool)
    {F : Type} [Field F] (Fs : Cosheaf X F) (m : Fin t → Bool → ℕ) where
  xf : X → X
  xf_le : ∀ f, xf f ≤ f
  xf_vertex : ∀ f, fdim φ (xf f) = 0
  G : ∀ (f : X) (i : Fin t), Matrix (EdgeType φ (xf f) i) (Fin (m i (bit φ f i))) F
  G_inj : ∀ f i, i ∈ codir φ f → Function.Injective (G f i).mulVec
  Ψ : ∀ f g : X, f ≤ g → (Fin (Fs.d g) → F) ≃ₗ[F] (TensorIdx φ m f g → F)

/-- The **local code** `C_{f,i} := im G_{f,i} ⊆ F^{Ω_{f,i}}` (arXiv:2609.20780, §4.3, p.17). -/
noncomputable def localCode {X : Type} [PartialOrder X] [Fintype X] {t : ℕ}
    {φ : X → Fin t → Option Bool} {F : Type} [Field F] {Fs : Cosheaf X F} {m : Fin t → Bool → ℕ}
    (D : BaseCodeData φ Fs m) (f : X) (i : Fin t) :
    Submodule F (EdgeType φ (D.xf f) i → F) :=
  LinearMap.range (D.G f i).mulVecLin

open Classical in
/-- **Compatibility** of base-code data with the cosheaf, Gay–Jeronimo, arXiv:2609.20780 (held
version), Definition 4.8, Equation (4.4), p.17: for every `f`, `T ⊆ J_f`, `ω ∈ Ω_{f,T}`,
`j ∈ J_f ∖ T` and `ω_j ∈ Ω_{f,j}`, the faces `g := θ_{f,x_f}(T, ω)` and
`h := θ_{f,x_f}(T ∪ {j}, (ω, ω_j))` satisfy
`Ψ_{f,h} R_{hg} Ψ_{f,g}^{−1} = (ev_{ω_j} ∘ G_{f,j}) ⊗ ⨂_{i ∈ J_f ∖ (T∪{j})} id_{U_{f,i}}`.

**Formalization Note.** `θ_{f,x}(T, e)` is "the unique face of type `dir(f) ∪ T` containing `f` and
every `e_i`" (Lemma 4.3, p.15); the condition is imposed on every pair `g ≤ h` with these defining
properties. The right-hand side, applied to a tensor `y` on `∏_{i∈codir(g)}`, is
`α ↦ ∑_β [β|_{codir(h)} = α] G_{f,j}(ω_j, β_j) y(β)`. -/
def IsCompatible {X : Type} [PartialOrder X] [Fintype X] {t : ℕ}
    {φ : X → Fin t → Option Bool} {F : Type} [Field F] {Fs : Cosheaf X F} {m : Fin t → Bool → ℕ}
    (D : BaseCodeData φ Fs m) : Prop :=
  ∀ (f : X) (T : Finset (Fin t)), T ⊆ codir φ f →
  ∀ ω : Fin t → X, (∀ i ∈ T, dir φ (ω i) = {i} ∧ D.xf f ≤ ω i) →
  ∀ j : Fin t, j ∈ codir φ f → j ∉ T →
  ∀ ωj : EdgeType φ (D.xf f) j,
  ∀ (g h : X) (hfg : f ≤ g) (hgh : g ≤ h),
    dir φ g = dir φ f ∪ T → (∀ i ∈ T, ω i ≤ g) →
    dir φ h = dir φ f ∪ insert j T → (∀ i ∈ T, ω i ≤ h) → ωj.1 ≤ h →
    ∀ (y : TensorIdx φ m f g → F) (α : TensorIdx φ m f h),
      D.Ψ f h (hfg.trans hgh) ((Fs.R g h).mulVec ((D.Ψ f g hfg).symm y)) α =
        ∑ β : TensorIdx φ m f g,
          if (∀ (i : Fin t) (hi : i ∈ codir φ h) (hi' : i ∈ codir φ g), β ⟨i, hi'⟩ = α ⟨i, hi⟩)
          then (if hj : j ∈ codir φ g then D.G f j ωj (β ⟨j, hj⟩) else 0) * y β
          else 0

end GoodQLTC



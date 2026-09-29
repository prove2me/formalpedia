-- Prove2me | Definitions.Def_RepTheory_SchwartzBruhat_CheckConvolution
-- name    : RepTheory_SchwartzBruhat_CheckConvolution
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/308ba5ac-ff34-5bf8-b574-b0e0b9b5ddf7
-- title:
--   Check operator and convolution on Schwartz–Bruhat test functions
-- statement:
--   Throughout, $G$ is a topological group. The ambient space is [`SchwartzBruhatSpace.testSpace G`](../def/LanglandsTunnell_SchwartzBruhatSpace.html#L17), the $\mathbb{C}$-submodule of all functions $G \to \mathbb{C}$ that are locally constant and have compact support.
--
--   The first part treats transport along homeomorphisms: if $\sigma : X \simeq X'$ is a homeomorphism and $f : X' \to \mathbb{C}$ is locally constant with compact support, then so is $f \circ \sigma$. For a bicontinuous group automorphism $\sigma$ of $G$ (an element of `G ≃ₜ* G`), `checkHomeomorph σ` is the self-homeomorphism of $G$ obtained by inversion followed by $\sigma^{-1}$, that is $h \mapsto \sigma^{-1}(h^{-1})$, and `check σ` is the $\mathbb{C}$-linear endomorphism of `testSpace G` sending $\varphi$ to the function $h \mapsto \varphi(\sigma^{-1}(h^{-1}))$; `check_apply` records this value.
--
--   The second part concerns multiplicative convolution, $(\mathrm{mulConv}\ \mu\ f\ g)(x) = \int_G f(y)\,g(y^{-1}x)\,d\mu(y)$. A preliminary result states a uniformity property of test functions: if $\varphi : G \to \mathbb{C}$ is locally constant with compact support, there is a neighbourhood $W$ of $1$ such that $\varphi(gk) = \varphi(g)$ for all $k \in W$ and all $g \in G$; the proof covers the support by finitely many local-constancy neighbourhoods and intersects, then symmetrises by replacing $W$ by $W \cap W^{-1}$ to handle $g$ outside the support. With $G$ in addition Hausdorff and equipped with a measurable structure, and $\mu$ a measure on $G$, `mulConv_mem_testSpace` asserts that the convolution of two members of `testSpace G` is again locally constant with compact support, the local constancy coming from the right-translation invariance of the second factor. Finally `convolution μ φ ψ` packages this convolution as an element of `testSpace G`, with `coe_convolution` identifying its underlying function with $\mathrm{mulConv}\ \mu\ \varphi\ \psi$.
--
--   **Relation to Mathlib.** Mathlib's Schwartz space (`SchwartzMap`) is the archimedean one; the space of locally constant compactly supported functions used here, and the multiplicative convolution $\int f(y) g(y^{-1}x)\,d\mu(y)$, are the project's own, Mathlib's `MeasureTheory.convolution` being formulated for additive groups. The transport and support lemmas are assembled from Mathlib's `IsLocallyConstant` and `HasCompactSupport` API.
--
--   **Where it is used.** These test functions and their convolution product supply the Hecke-algebra formalism used on the automorphic side of the Langlands–Tunnell theorem, which provides the modularity of the mod $3$ representation that starts the induction in the proof of Fermat's Last Theorem. The operator $\varphi \mapsto \varphi(\sigma^{-1}(\cdot^{-1}))$ attached to a bicontinuous automorphism $\sigma$ is the twisting operation appearing in base-change comparisons.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_RepTheory_SchwartzBruhat_CheckConvolution.lean

import Definitions.Def_LanglandsTunnell_SchwartzBruhatSpace
import Definitions.Def_RepTheory_MulConvolution
import Mathlib.Topology.Algebra.ContinuousMonoidHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace TestFunctionAction

section Transport

variable {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']

private theorem comp_homeomorph_mem (σ : X ≃ₜ X') {f : X' → ℂ} (hf : f ∈ SchwartzBruhatSpace.testSpace X') :
    f ∘ σ ∈ SchwartzBruhatSpace.testSpace X :=
  ⟨(SchwartzBruhatSpace.isLocallyConstant_of_mem hf).comp_continuous σ.continuous,
    (SchwartzBruhatSpace.hasCompactSupport_of_mem hf).comp_homeomorph σ⟩

end Transport
section Check

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def checkHomeomorph (σ : G ≃ₜ* G) : G ≃ₜ G :=
  (Homeomorph.inv G).trans σ.symm.toHomeomorph

theorem checkHomeomorph_apply (σ : G ≃ₜ* G) (h : G) : checkHomeomorph σ h = σ.symm h⁻¹ := rfl

noncomputable def check (σ : G ≃ₜ* G) :
    SchwartzBruhatSpace.testSpace G →ₗ[ℂ] SchwartzBruhatSpace.testSpace G where
  toFun φ := ⟨fun h => (φ : G → ℂ) (σ.symm h⁻¹),
    comp_homeomorph_mem (checkHomeomorph σ) φ.2⟩
  map_add' φ ψ := by ext h; rfl
  map_smul' c φ := by ext h; rfl

@[simp]
theorem check_apply (σ : G ≃ₜ* G) (φ : SchwartzBruhatSpace.testSpace G) (h : G) :
    (check σ φ : G → ℂ) h = (φ : G → ℂ) (σ.symm h⁻¹) := rfl

end Check

section Convolution

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem exists_mem_nhds_one_right_invariant {φ : G → ℂ} (hlc : IsLocallyConstant φ)
    (hcs : HasCompactSupport φ) :
    ∃ W ∈ 𝓝 (1 : G), ∀ k ∈ W, ∀ g, φ (g * k) = φ g := by
  have hloc : ∀ x : G, ∃ V ∈ 𝓝 x, ∃ W ∈ 𝓝 (1 : G), ∀ g ∈ V, ∀ k ∈ W, φ (g * k) = φ g := by
    intro x
    obtain ⟨U, hUo, hxU, hUc⟩ := hlc.exists_open x
    have hpre : (fun p : G × G => p.1 * p.2) ⁻¹' U ∈ 𝓝 ((x, 1) : G × G) :=
      (hUo.preimage continuous_mul).mem_nhds (by simpa using hxU)
    obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.1 hpre
    refine ⟨V, hV, W, hW, fun g hg k hk => ?_⟩
    have h1 : g * k ∈ U := hVW (Set.mk_mem_prod hg hk)
    have h2 : g * 1 ∈ U := hVW (Set.mk_mem_prod hg (mem_of_mem_nhds hW))
    rw [hUc _ h1, ← hUc _ h2, mul_one]
  choose V hV W hW hVW using hloc
  obtain ⟨t, -, ht⟩ := IsCompact.elim_nhds_subcover (s := tsupport φ) hcs V fun x _ => hV x
  set W₀ : Set G := ⋂ x ∈ t, W x with hW₀
  have hW₀n : W₀ ∈ 𝓝 (1 : G) := (biInter_finset_mem t).2 fun x _ => hW x
  have hkey : ∀ k ∈ W₀, ∀ g ∈ tsupport φ, φ (g * k) = φ g := by
    intro k hk g hg
    obtain ⟨x, hxt, hgx⟩ := Set.mem_iUnion₂.1 (ht hg)
    exact hVW x g hgx k (Set.mem_iInter₂.1 hk x hxt)
  refine ⟨W₀ ∩ W₀⁻¹, inter_mem hW₀n (inv_mem_nhds_one G hW₀n), fun k hk g => ?_⟩
  by_cases hg : g ∈ tsupport φ
  · exact hkey k hk.1 g hg
  · by_cases hgk : g * k ∈ tsupport φ
    · have := hkey k⁻¹ (Set.mem_inv.1 hk.2) (g * k) hgk
      rwa [mul_inv_cancel_right, eq_comm] at this
    · rw [image_eq_zero_of_notMem_tsupport hg, image_eq_zero_of_notMem_tsupport hgk]

variable [T2Space G] [MeasurableSpace G]

theorem mulConv_mem_testSpace (μ : Measure G) {φ ψ : G → ℂ}
    (hφ : φ ∈ SchwartzBruhatSpace.testSpace G) (hψ : ψ ∈ SchwartzBruhatSpace.testSpace G) :
    MulConvolution.mulConv μ φ ψ ∈ SchwartzBruhatSpace.testSpace G := by
  refine ⟨MulConvolution.isLocallyConstant_mulConv μ φ ψ ?_,
    MulConvolution.hasCompactSupport_mulConv μ hφ.2 hψ.2⟩
  obtain ⟨U, hU, hUψ⟩ := exists_mem_nhds_one_right_invariant hψ.1 hψ.2
  exact ⟨U, hU, fun u hu x => hUψ u hu x⟩

noncomputable def convolution (μ : Measure G) (φ ψ : SchwartzBruhatSpace.testSpace G) :
    SchwartzBruhatSpace.testSpace G :=
  ⟨MulConvolution.mulConv μ φ ψ, mulConv_mem_testSpace μ φ.2 ψ.2⟩

@[simp]
theorem coe_convolution (μ : Measure G) (φ ψ : SchwartzBruhatSpace.testSpace G) :
    (convolution μ φ ψ : G → ℂ) = MulConvolution.mulConv μ φ ψ := rfl

end Convolution

end TestFunctionAction



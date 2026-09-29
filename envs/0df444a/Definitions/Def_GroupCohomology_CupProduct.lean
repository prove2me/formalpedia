-- Prove2me | Definitions.Def_GroupCohomology_CupProduct
-- name    : GroupCohomology_CupProduct
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/8d7f0a5b-1d6a-596c-b015-9d25efc9f6ab
-- title:
--   Cup product in degrees (1,1) and local Tate duality predicates
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, and let $A$, $B$, $N$ be $k$-linear representations of $G$. [`Rep.IsEquivariantBilinear A B N φ`](../def/GroupCohomology_CupProduct.html#L13) says of a $k$-bilinear map $φ \colon A \times B \to N$ that $φ(ρ_A(g)a, ρ_B(g)b) = ρ_N(g)\,φ(a,b)$ for all $g \in G$, $a \in A$, $b \in B$. Along such a $φ$, `cupCochain` is the inhomogeneous $2$-cochain attached to functions $f \colon G \to A$, $g \colon G \to B$ by $(s,t) \mapsto φ(f(s), ρ_B(s) g(t))$. It is proved that this cochain is a $2$-cocycle when $f$ and $g$ are $1$-cocycles, and `cup` packages this as a $k$-bilinear map $Z^1(G,A) \times Z^1(G,B) \to Z^2(G,N)$. Two further lemmas produce explicit primitives: if $f = d^0_1(a)$ then $f \smile g$ is the coboundary of $t \mapsto φ(a, g(t))$, and if $g = d^0_1(b)$ then $-(f \smile g)$ is the coboundary of $s \mapsto φ(f(s), ρ_B(s) b)$. A descent gadget (`H1desc`, together with surjectivity of $Z^1 \to H^1$ and the resulting extensionality principle for linear maps out of $H^1$) factors any $k$-linear map on $1$-cocycles vanishing on $1$-coboundaries through $H^1$; applying it in each variable gives `cupH1`, the bilinear map $H^1(G,A) \times H^1(G,B) \to H^2(G,N)$.
--
--   The remaining declarations are predicates. `IsCupProductPairing φ hφ inv P`, for a functional $\mathrm{inv} \colon H^2(G,N) \to k$ and a bilinear $P \colon H^1(G,A) \times H^1(G,B) \to k$, asserts $P([f],[g]) = \mathrm{inv}([f \smile g])$ for all $1$-cocycles $f$, $g$; since the projections are surjective this pins $P$ uniquely. The `Prop`-valued structure `IsLocalTateDatum` carries as fields: $φ$ separates points in each variable, $\dim_k H^2(G,N) = 1$, $\mathrm{inv} \neq 0$, and the pinning condition. Over a field $k$, `IsLocalTateDuality` adds to a local Tate datum the finite-dimensionality of $H^1(G,A)$ and of $H^1(G,B)$ and nondegeneracy of $P$; these classical theorems are thus recorded as hypotheses, to be supplied by arithmetic input. Finally, for a family of group homomorphisms $\mathrm{loc}_v \colon Γ_v \to Γ$, representations $M$, $M'$ of $Γ$ and pairings on $H^1(Γ_v, M)$, $H^1(Γ_v, M')$ (cohomology of the restricted representations), `IsLocalTatePairingFamily` and `IsLocalTateDualityFamily` assert that for each $v$ there exist $N_v$, an equivariant bilinear $φ_v$ and a functional $\mathrm{inv}_v$ exhibiting the given pairing at $v$ as a local Tate datum, respectively as a local Tate duality.
--
--   **Relation to Mathlib.** Mathlib's low-degree inhomogeneous cochain API for group cohomology (`cocycles₁`, `cocycles₂`, `coboundaries₁`, `H1`, `H2`, the projections `H1π`, `H2π`, the differentials `d₀₁`, `d₁₂`, and `Rep.res`) is used throughout; the explicit degree-$(1,1)$ cup product along a bilinear equivariant pairing is built directly from that API, and the local Tate datum and local Tate duality predicates are the project's own.
--
--   **Where it is used.** The pairings axiomatised here are the local Tate pairings $H^1(G_v, M) \times H^1(G_v, M') \to k$ used to cut out the dual Selmer group by orthogonality of local conditions, as in the Greenberg–Wiles formula that controls Selmer group sizes in the modularity lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_CupProduct.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory Module

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

def IsEquivariantBilinear (A B N : Rep k G) (φ : A →ₗ[k] B →ₗ[k] N) : Prop :=
  ∀ (g : G) (a : A) (b : B), φ (A.ρ g a) (B.ρ g b) = N.ρ g (φ a b)

end Rep

namespace groupCohomology

section CupProduct

variable {k G : Type u} [CommRing k] [Group G] {A B N : Rep k G}

private lemma ρ_mul_apply (M : Rep k G) (s t : G) (x : M) :
    M.ρ (s * t) x = M.ρ s (M.ρ t x) := by
  rw [Rep.ρ_mul]; rfl

variable (φ : A →ₗ[k] B →ₗ[k] N)

def cupCochain (f : G → A) (g : G → B) : G × G → N :=
  fun p => φ (f p.1) (B.ρ p.1 (g p.2))

@[simp]
lemma cupCochain_apply (f : G → A) (g : G → B) (s t : G) :
    cupCochain φ f g (s, t) = φ (f s) (B.ρ s (g t)) := rfl

variable (hφ : Rep.IsEquivariantBilinear A B N φ)

include hφ in

private theorem cupCochain_mem_cocycles₂ (f : cocycles₁ A) (g : cocycles₁ B) :
    cupCochain φ (⇑f) (⇑g) ∈ cocycles₂ N := by
  rw [mem_cocycles₂_iff]
  intro s t u
  simp only [cupCochain_apply]

  rw [(mem_cocycles₁_iff (⇑f)).1 f.2 s t, (mem_cocycles₁_iff (⇑g)).1 g.2 t u,
    ← hφ s (f t) (B.ρ t (g u))]
  simp only [map_add, LinearMap.add_apply, ρ_mul_apply]
  abel

noncomputable def cup : cocycles₁ A →ₗ[k] cocycles₁ B →ₗ[k] cocycles₂ N :=
  LinearMap.mk₂ k
    (fun f g => ⟨cupCochain φ (⇑f) (⇑g), cupCochain_mem_cocycles₂ φ hφ f g⟩)
    (fun f f' g => by
      ext s t
      show φ (f s + f' s) (B.ρ s (g t)) = φ (f s) (B.ρ s (g t)) + φ (f' s) (B.ρ s (g t))
      rw [map_add, LinearMap.add_apply])
    (fun c f g => by
      ext s t
      show φ (c • f s) (B.ρ s (g t)) = c • φ (f s) (B.ρ s (g t))
      rw [map_smul, LinearMap.smul_apply])
    (fun f g g' => by
      ext s t
      show φ (f s) (B.ρ s (g t + g' t)) = φ (f s) (B.ρ s (g t)) + φ (f s) (B.ρ s (g' t))
      rw [map_add, map_add])
    (fun c f g => by
      ext s t
      show φ (f s) (B.ρ s (c • g t)) = c • φ (f s) (B.ρ s (g t))
      rw [map_smul, map_smul])

@[simp]
lemma cup_apply (f : cocycles₁ A) (g : cocycles₁ B) (s t : G) :
    (cup φ hφ f g) (s, t) = φ (f s) (B.ρ s (g t)) := rfl

lemma cup_coe (f : cocycles₁ A) (g : cocycles₁ B) :
    ⇑(cup φ hφ f g) = cupCochain φ (⇑f) (⇑g) := rfl

include hφ in

private theorem cup_mem_coboundaries₂_left {f : cocycles₁ A} (hf : ⇑f ∈ coboundaries₁ A)
    (g : cocycles₁ B) : ⇑(cup φ hφ f g) ∈ coboundaries₂ N := by
  obtain ⟨a, ha⟩ := hf
  have hfs : ∀ s : G, f s = A.ρ s a - a := fun s => by rw [← ha, d₀₁_hom_apply]
  refine ⟨fun t => φ a (g t), funext fun p => ?_⟩
  obtain ⟨s, t⟩ := p
  rw [d₁₂_hom_apply]
  show N.ρ s (φ a (g t)) - φ a (g (s * t)) + φ a (g s) = φ (f s) (B.ρ s (g t))
  rw [hfs s, (mem_cocycles₁_iff (⇑g)).1 g.2 s t, ← hφ s a (g t)]
  simp only [map_add, map_sub, LinearMap.sub_apply]
  abel

include hφ in

private theorem cup_mem_coboundaries₂_right (f : cocycles₁ A) {g : cocycles₁ B}
    (hg : ⇑g ∈ coboundaries₁ B) : ⇑(cup φ hφ f g) ∈ coboundaries₂ N := by
  obtain ⟨b, hb⟩ := hg
  have hgs : ∀ t : G, g t = B.ρ t b - b := fun t => by rw [← hb, d₀₁_hom_apply]
  rw [← neg_mem_iff]
  refine ⟨fun s => φ (f s) (B.ρ s b), funext fun p => ?_⟩
  obtain ⟨s, t⟩ := p
  rw [d₁₂_hom_apply]
  show N.ρ s (φ (f t) (B.ρ t b)) - φ (f (s * t)) (B.ρ (s * t) b) + φ (f s) (B.ρ s b)
      = -(φ (f s) (B.ρ s (g t)))
  rw [hgs t, (mem_cocycles₁_iff (⇑f)).1 f.2 s t, ← hφ s (f t) (B.ρ t b),
    ρ_mul_apply B s t b]
  simp only [map_add, map_sub, LinearMap.add_apply]
  abel

section DescentGadget

variable {W : Type u} [AddCommGroup W] [Module k W]

variable (A) in

private lemma H1π_surjective : Function.Surjective (H1π A).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

private theorem H1_hom_ext {F F' : H1 A →ₗ[k] W}
    (h : ∀ x : cocycles₁ A, F (H1π A x) = F' (H1π A x)) : F = F' :=
  LinearMap.ext fun y => H1_induction_on y h

noncomputable def H1desc (F : cocycles₁ A →ₗ[k] W)
    (hF : ∀ x : cocycles₁ A, ⇑x ∈ coboundaries₁ A → F x = 0) : H1 A →ₗ[k] W :=
  (LinearMap.ker (H1π A).hom).liftQ F
      (fun x hx => LinearMap.mem_ker.2
        (hF x ((H1π_eq_zero_iff x).1 (LinearMap.mem_ker.1 hx)))) ∘ₗ
    ((H1π A).hom.quotKerEquivOfSurjective (H1π_surjective A)).symm.toLinearMap

@[simp]
lemma H1desc_H1π (F : cocycles₁ A →ₗ[k] W)
    (hF : ∀ x : cocycles₁ A, ⇑x ∈ coboundaries₁ A → F x = 0) (x : cocycles₁ A) :
    H1desc F hF (H1π A x) = F x := by
  unfold H1desc
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

end DescentGadget

private noncomputable def cupRight (f : cocycles₁ A) : H1 B →ₗ[k] H2 N :=
  H1desc ((H2π N).hom ∘ₗ cup φ hφ f)
    (fun _ hg => (H2π_eq_zero_iff _).2 (cup_mem_coboundaries₂_right φ hφ f hg))

private lemma cupRight_H1π (f : cocycles₁ A) (g : cocycles₁ B) :
    cupRight φ hφ f (H1π B g) = H2π N (cup φ hφ f g) :=
  H1desc_H1π _ _ g

noncomputable def cupH1 : H1 A →ₗ[k] H1 B →ₗ[k] H2 N :=
  H1desc
    { toFun := cupRight φ hφ
      map_add' := fun f f' => H1_hom_ext fun g =>
        ((cupRight_H1π φ hφ (f + f') g).trans (by
            rw [map_add, LinearMap.add_apply, map_add])).trans
          (congrArg₂ (· + ·) (cupRight_H1π φ hφ f g) (cupRight_H1π φ hφ f' g)).symm
      map_smul' := fun c f => H1_hom_ext fun g =>
        ((cupRight_H1π φ hφ (c • f) g).trans (by
            rw [map_smul, LinearMap.smul_apply, map_smul])).trans
          (congrArg (c • ·) (cupRight_H1π φ hφ f g)).symm }
    (fun f hf => H1_hom_ext fun g =>
      (cupRight_H1π φ hφ f g).trans
        ((H2π_eq_zero_iff _).2 (cup_mem_coboundaries₂_left φ hφ hf g)))

def IsCupProductPairing (inv : H2 N →ₗ[k] k) (P : H1 A →ₗ[k] H1 B →ₗ[k] k) : Prop :=
  ∀ (f : cocycles₁ A) (g : cocycles₁ B),
    P (H1π A f) (H1π B g) = inv (H2π N (cup φ hφ f g))

structure IsLocalTateDatum (inv : H2 N →ₗ[k] k) (P : H1 A →ₗ[k] H1 B →ₗ[k] k) : Prop where

  left_nondegenerate : ∀ a : A, (∀ b : B, φ a b = 0) → a = 0

  right_nondegenerate : ∀ b : B, (∀ a : A, φ a b = 0) → b = 0

  finrank_H2 : Module.finrank k (H2 N) = 1

  inv_ne_zero : inv ≠ 0

  cup_eq : IsCupProductPairing φ hφ inv P

end CupProduct

section Arithmetic

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)

def IsLocalTatePairingFamily : Prop :=
  ∀ v : ι, ∃ (Nv : Rep k (Γv v))
    (φv : Rep.res (loc v) M →ₗ[k] Rep.res (loc v) M' →ₗ[k] Nv)
    (hφv : Rep.IsEquivariantBilinear _ _ _ φv) (invv : H2 Nv →ₗ[k] k),
      IsLocalTateDatum φv hφv invv (pairing v)

end Arithmetic

section LocalDuality

variable {k G : Type u} [Field k] [Group G] {A B N : Rep k G}
variable (φ : A →ₗ[k] B →ₗ[k] N)
variable (hφ : Rep.IsEquivariantBilinear A B N φ)

structure IsLocalTateDuality (inv : H2 N →ₗ[k] k) (P : H1 A →ₗ[k] H1 B →ₗ[k] k) : Prop where

  toIsLocalTateDatum : IsLocalTateDatum φ hφ inv P

  finite_H1_left : FiniteDimensional k (H1 A)

  finite_H1_right : FiniteDimensional k (H1 B)

  nondegenerate : P.Nondegenerate

end LocalDuality

section Family

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} [Fintype ι] {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)

def IsLocalTateDualityFamily : Prop :=
  ∀ v : ι, ∃ (Nv : Rep k (Γv v))
    (φv : Rep.res (loc v) M →ₗ[k] Rep.res (loc v) M' →ₗ[k] Nv)
    (hφv : Rep.IsEquivariantBilinear _ _ _ φv) (invv : H2 Nv →ₗ[k] k),
      IsLocalTateDuality φv hφv invv (pairing v)

end Family

end groupCohomology



-- Prove2me | Definitions.Def_RPLib_S4_EtShGalEt
-- name    : RPLib_S4_EtShGalEt
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:12:33.43675+00:00
-- url     : https://prove2.me/theorems/45ed9a2d-8d82-443f-854c-e83d1cbaf83d
-- title:
--   Galois covers with trivial inertia are etale (Chase-Harrison-Rosenberg)
-- statement:
--   Let a finite group $G$ act on a commutative ring $B$ with ring of invariants $A = B^G$, $A \to B$ injective and finite, and suppose that every inertia group $I(\mathfrak m) = \{\sigma \in G : \sigma(b) - b \in \mathfrak m \text{ for all } b\}$ at a maximal ideal $\mathfrak m$ of $B$ is trivial. Then there are $x_1, \dots, x_n, y_1, \dots, y_n \in B$ with $$\sum_i x_i\,\sigma(y_i) = \begin{cases} 1 & \sigma = 1 \\ 0 & \sigma \ne 1, \end{cases}$$ hence $B$ is a projective $A$-module (dual basis $b = \sum_i \mathrm{tr}(y_i b)\,x_i$), the map $$B \otimes_A B \to \prod_{\sigma \in G} B, \qquad b \otimes b' \mapsto (b\,\sigma(b'))_{\sigma}$$ is an isomorphism, and $A \to B$ is formally unramified and etale. For the Galois covers of the library this gives the etale morphism $\mathrm{Spec}\,B \to \mathrm{Spec}\,A$ and the torsor isomorphism above.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   S. U. Chase, D. K. Harrison, A. Rosenberg, Galois theory and Galois cohomology of commutative rings, Mem. Amer. Math. Soc. 52 (1965), Theorem 1.3; A. Grothendieck, Revetements etales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Expose V

import Mathlib
import Definitions.Def_RPLib_S4_GalCover

/-!
# S4-EtSheaves, part O10d-1: Galois covers with trivial inertia are etale (Chase-Harrison-Rosenberg)

Let a finite group `G` act on `B` with `A = B^G` (`IsGaloisGroup G A B`), `A → B` injective and finite, and every
inertia group at a maximal ideal of `B` trivial. Then (Chase-Harrison-Rosenberg, Thm 1.3):

* `exists_chr`: there are `x y : Fin n → B` with `∑ x_i y_i = 1` and `∑ x_i σ(y_i) = 0` for `σ ≠ 1` (`CHR`);
* `projective`: `B` is a projective `A`-module (dual basis `b = ∑ tr(y_i b) x_i`, `sum_trL_smul`);
* `phi_injective`, `phi_surjective`, `torsorEquiv`: `B ⊗_A B ≅ Π_G B`, `b ⊗ b' ↦ (b σ(b'))_σ`;
* `formallyUnramified`, HEADLINE `etale`: `A → B` is etale.

For a `GalCover` `C` this gives `GalCover.etale C : Algebra.Etale A C.B`, the scheme form `GalCover.etale_spec`, and
the torsor isomorphism `GalCover.torsorEquiv C : C.B ⊗[A] C.B ≃ₐ[A] (C.G → C.B)`.
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtSheaves

namespace GalEt

/-- Chase-Harrison-Rosenberg elements: `∑ x_i y_i = 1` and `∑ x_i σ(y_i) = 0` for `σ ≠ 1`. -/
structure CHR {B : Type*} [CommRing B] (G : Type*) [Group G] [MulSemiringAction G B] {n : ℕ} (x y : Fin n → B) :
    Prop where
  one : ∑ i, x i * y i = 1
  ne : ∀ σ : G, σ ≠ 1 → ∑ i, x i * σ • y i = 0

section Pair

variable {B G : Type*} [CommRing B] [Group G] [MulSemiringAction G B]

/-- Trivial inertia at every maximal ideal: for `σ ≠ 1`, the elements `σ b - b` generate the unit ideal. -/
theorem one_mem_span_sub (hI : ∀ m : Ideal B, m.IsMaximal → m.inertia G = ⊥) {σ : G} (hσ : σ ≠ 1) :
    (1 : B) ∈ Ideal.span (Set.range fun b : B => σ • b - b) := by
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ ((Ideal.ne_top_iff_one _).mpr h)
  have hmem : σ ∈ m.inertia G := fun x => hle (Ideal.subset_span ⟨x, rfl⟩)
  rw [hI m hm, Subgroup.mem_bot] at hmem
  exact hσ hmem

/-- Reindex a finite family of pairs by `Fin n`. -/
theorem exists_fin_of_fintype {ι : Type*} [Fintype ι] (a b : ι → B) :
    ∃ (n : ℕ) (a' b' : Fin n → B), ∀ f : B → B → B, ∑ i, f (a' i) (b' i) = ∑ i, f (a i) (b i) := by
  classical
  let e := Fintype.equivFin ι
  exact ⟨Fintype.card ι, a ∘ e.symm, b ∘ e.symm, fun f => e.symm.sum_comp (fun i => f (a i) (b i))⟩

/-- CHR (1): for `σ ≠ 1` there are `a b` with `∑ a_j b_j = 1` and `∑ a_j σ(b_j) = 0`. -/
theorem exists_pair (hI : ∀ m : Ideal B, m.IsMaximal → m.inertia G = ⊥) {σ : G} (hσ : σ ≠ 1) :
    ∃ (n : ℕ) (a b : Fin n → B), ∑ i, a i * b i = 1 ∧ ∑ i, a i * σ • b i = 0 := by
  classical
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp (one_mem_span_sub hI hσ)
  have hc' : ∑ i : c.support, c i * σ • (i : B) - ∑ i : c.support, c i * (i : B) = 1 := by
    rw [Finset.sum_coe_sort c.support (fun i => c i * σ • i), Finset.sum_coe_sort c.support (fun i => c i * i),
      ← Finset.sum_sub_distrib]
    simpa only [Finsupp.sum, mul_sub] using hc
  let a : Option c.support → B := fun o => o.elim (∑ i : c.support, c i * σ • (i : B)) fun i => -c i
  let b : Option c.support → B := fun o => o.elim 1 fun i => (i : B)
  obtain ⟨n, a', b', h⟩ := exists_fin_of_fintype a b
  refine ⟨n, a', b', ?_, ?_⟩
  · rw [h (fun u v => u * v), Fintype.sum_option]
    simp only [a, b, Option.elim, neg_mul, Finset.sum_neg_distrib, mul_one]
    linear_combination hc'
  · rw [h (fun u v => u * σ • v), Fintype.sum_option]
    simp only [a, b, Option.elim, neg_mul, Finset.sum_neg_distrib, smul_one, mul_one]
    ring

/-- CHR (2): trivial inertia at the maximal ideals gives CHR elements (product of the pairs over `σ ≠ 1`). -/
theorem exists_chr [Finite G] (hI : ∀ m : Ideal B, m.IsMaximal → m.inertia G = ⊥) :
    ∃ (n : ℕ) (x y : Fin n → B), CHR G x y := by
  classical
  have := Fintype.ofFinite G
  choose n a b hab using fun τ : {τ : G // τ ≠ 1} => exists_pair hI τ.2
  let x : ((τ : {τ : G // τ ≠ 1}) → Fin (n τ)) → B := fun f => ∏ τ, a τ (f τ)
  let y : ((τ : {τ : G // τ ≠ 1}) → Fin (n τ)) → B := fun f => ∏ τ, b τ (f τ)
  obtain ⟨N, x', y', h⟩ := exists_fin_of_fintype x y
  have hprod : ∀ σ : G, ∑ i, x' i * σ • y' i = ∏ τ, ∑ j, a τ j * σ • b τ j := by
    intro σ
    calc ∑ i, x' i * σ • y' i = ∑ f, x f * σ • y f := h (fun u v => u * σ • v)
      _ = ∑ f : ((τ : {τ : G // τ ≠ 1}) → Fin (n τ)), ∏ τ, a τ (f τ) * σ • b τ (f τ) :=
          Finset.sum_congr rfl fun f _ => by
            simp only [x, y, Finset.smul_prod', Finset.prod_mul_distrib]
      _ = ∏ τ, ∑ j, a τ j * σ • b τ j := (Fintype.prod_sum (fun τ j => a τ j * σ • b τ j)).symm
  refine ⟨N, x', y', ⟨?_, fun σ hσ => ?_⟩⟩
  · have h1 := hprod 1
    simp only [one_smul] at h1
    rw [h1]
    exact Finset.prod_eq_one fun τ _ => by simpa only [one_smul] using (hab τ).1
  · rw [hprod σ]
    exact Finset.prod_eq_zero (Finset.mem_univ ⟨σ, hσ⟩) (hab ⟨σ, hσ⟩).2

end Pair

section Trace

variable (A : Type*) {B : Type*} (G : Type*) [CommRing A] [CommRing B] [Algebra A B] [Group G] [Fintype G]
  [MulSemiringAction G B] [IsGaloisGroup G A B]

theorem smul_sum_smul (τ : G) (b : B) : τ • ∑ σ : G, σ • b = ∑ σ : G, σ • b := by
  rw [Finset.smul_sum]
  simp_rw [smul_smul]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun _ => rfl

/-- The trace `∑_σ σ(b)`, as an element of `A = B^G`. -/
def trA (b : B) : A :=
  (Algebra.IsInvariant.isInvariant (A := A) (G := G) (∑ σ : G, σ • b) fun τ => smul_sum_smul G τ b).choose

theorem algebraMap_trA (b : B) : algebraMap A B (trA A G b) = ∑ σ : G, σ • b :=
  (Algebra.IsInvariant.isInvariant (A := A) (G := G) (∑ σ : G, σ • b) fun τ => smul_sum_smul G τ b).choose_spec

variable [FaithfulSMul A B]

/-- The trace as an `A`-linear map `B → A`. -/
def trL : B →ₗ[A] A where
  toFun := trA A G
  map_add' b c := FaithfulSMul.algebraMap_injective A B (by
    simp only [map_add, algebraMap_trA, smul_add, Finset.sum_add_distrib])
  map_smul' a b := FaithfulSMul.algebraMap_injective A B (by
    rw [algebraMap_trA, RingHom.id_apply, smul_eq_mul, map_mul, algebraMap_trA, ← Algebra.smul_def,
      Finset.smul_sum]
    exact Finset.sum_congr rfl fun σ _ => smul_comm σ a b)

theorem algebraMap_trL (b : B) : algebraMap A B (trL A G b) = ∑ σ : G, σ • b := algebraMap_trA A G b

variable {A G} {n : ℕ} {x y : Fin n → B}

theorem sum_chr (h : CHR G x y) (c : G → B) : ∑ j, (∑ σ : G, σ • y j * c σ) * x j = c 1 := by
  calc _ = ∑ σ : G, c σ * ∑ j, x j * σ • y j := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun j _ => by ring
    _ = c 1 := by
        rw [Finset.sum_eq_single (1 : G) (fun σ _ hσ => by rw [h.ne σ hσ, mul_zero])
          (fun h1 => absurd (Finset.mem_univ _) h1)]
        simp only [one_smul, h.one, mul_one]

/-- The dual basis formula `b = ∑_j tr(y_j b) x_j`. -/
theorem sum_trL_smul (h : CHR G x y) (b : B) : ∑ j, trL A G (y j * b) • x j = b := by
  simp_rw [Algebra.smul_def, algebraMap_trL, smul_mul']
  exact sum_chr h (fun σ => σ • b) |>.trans (one_smul G b)

/-- CHR (3): `B` is a projective `A`-module. -/
theorem projective (h : CHR G x y) : Module.Projective A B := by
  refine Module.Projective.of_split (M := Fin n → A)
    (LinearMap.pi fun j => (trL A G).comp (LinearMap.mulLeft A (y j))) (Fintype.linearCombination A x) ?_
  refine LinearMap.ext fun b => ?_
  simp only [LinearMap.comp_apply, Fintype.linearCombination_apply, LinearMap.pi_apply,
    LinearMap.mulLeft_apply, LinearMap.id_apply]
  exact sum_trL_smul h b

end Trace

section Torsor

variable (A : Type*) {B : Type*} (G : Type*) [CommRing A] [CommRing B] [Algebra A B] [Group G]
  [MulSemiringAction G B] [SMulCommClass G A B]

/-- The map `B ⊗_A B → Π_G B`, `b ⊗ b' ↦ (b σ(b'))_σ`. -/
def phi : B ⊗[A] B →ₐ[A] (G → B) :=
  Algebra.TensorProduct.productMap (Pi.constAlgHom A G B)
    (AlgHom.pi fun σ : G => MulSemiringAction.toAlgHom A B σ)

@[simp] theorem phi_tmul (b b' : B) (σ : G) : phi A G (b ⊗ₜ[A] b') σ = b * σ • b' := rfl

variable {A G} [Fintype G] {n : ℕ} {x y : Fin n → B}

/-- A left inverse of `phi`. -/
def psi (x y : Fin n → B) (f : G → B) : B ⊗[A] B := ∑ j, (∑ σ : G, σ • y j * f σ) ⊗ₜ[A] x j

omit [SMulCommClass G A B] in
theorem psi_add (f g : G → B) : psi (A := A) x y (f + g) = psi x y f + psi x y g := by
  simp only [psi, Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.add_tmul]

variable [IsGaloisGroup G A B] [FaithfulSMul A B]

theorem psi_phi (h : CHR G x y) (u : B ⊗[A] B) : psi x y (phi A G u) = u := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [psi, map_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero, TensorProduct.zero_tmul]
  | tmul b b' =>
    unfold psi
    conv_rhs => rw [← sum_trL_smul (A := A) h b', TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← TensorProduct.smul_tmul, Algebra.smul_def (trL A G (y j * b')), algebraMap_trL, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [phi_tmul, smul_mul']
    ring
  | add u v hu hv => rw [map_add, psi_add, hu, hv]

theorem phi_injective (h : CHR G x y) : Function.Injective (phi A G (B := B)) := fun u v huv =>
  (psi_phi h u).symm.trans ((congrArg (psi x y) huv).trans (psi_phi h v))

omit [IsGaloisGroup G A B] [FaithfulSMul A B] in
theorem phi_surjective (h : CHR G x y) : Function.Surjective (phi A G (B := B)) := by
  intro f
  refine ⟨∑ τ : G, (f τ ⊗ₜ[A] (1 : B)) * ∑ i, x i ⊗ₜ[A] (τ⁻¹ • y i), funext fun σ => ?_⟩
  simp only [map_sum, map_mul, Finset.sum_apply, Pi.mul_apply, phi_tmul, smul_one, mul_one, smul_smul]
  rw [Finset.sum_eq_single σ (fun τ _ hτ => by
      rw [h.ne _ (fun h' => hτ (mul_inv_eq_one.mp h').symm), mul_zero])
    (fun h1 => absurd (Finset.mem_univ _) h1)]
  rw [mul_inv_cancel]
  simp only [one_smul, h.one, mul_one]

/-- The torsor isomorphism `B ⊗_A B ≅ Π_G B`. -/
def torsorEquiv (h : CHR G x y) : B ⊗[A] B ≃ₐ[A] (G → B) :=
  AlgEquiv.ofBijective (phi A G) ⟨phi_injective h, phi_surjective h⟩

theorem torsorEquiv_tmul (h : CHR G x y) (b b' : B) (σ : G) : torsorEquiv h (b ⊗ₜ[A] b') σ = b * σ • b' := rfl

end Torsor

section Etale

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B] [Group G]
  [MulSemiringAction G B] [IsGaloisGroup G A B] [FaithfulSMul A B] [Module.Finite A B]

/-- CHR (4): `A → B` is formally unramified. -/
theorem formallyUnramified [Fintype G] {n : ℕ} {x y : Fin n → B} (h : CHR G x y) :
    Algebra.FormallyUnramified A B := by
  have := projective (A := A) h
  have : Module.FinitePresentation A B := Module.finitePresentation_of_projective A B
  rw [Algebra.FormallyUnramified.iff_exists_tensorProduct]
  refine ⟨∑ i, x i ⊗ₜ[A] y i, fun s => phi_injective (A := A) h ?_, ?_⟩
  · rw [map_mul, map_zero]
    funext σ
    simp only [Pi.mul_apply, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, phi_tmul, one_mul, smul_one,
      mul_one, Pi.zero_apply]
    by_cases hσ : σ = 1
    · subst hσ; rw [one_smul, sub_self, zero_mul]
    · rw [h.ne σ hσ, mul_zero]
  · simp only [map_sum, Algebra.TensorProduct.lmul'_apply_tmul]
    exact h.one

/-- **HEADLINE (CHR 1.3).** A finite Galois extension `A = B^G ⊆ B` with trivial inertia at every maximal ideal is
etale. -/
theorem etale [Finite G] (hI : ∀ m : Ideal B, m.IsMaximal → m.inertia G = ⊥) : Algebra.Etale A B := by
  have := Fintype.ofFinite G
  obtain ⟨n, x, y, h⟩ := exists_chr hI
  have := projective (A := A) h
  have : Module.FinitePresentation A B := Module.finitePresentation_of_projective A B
  have := formallyUnramified (A := A) h
  exact Algebra.Etale.of_formallyUnramified_of_flat

end Etale

end GalEt

end RamanujanPetersson.EtSheaves

namespace RamanujanPetersson.GalCover

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)

/-- **A Galois cover is etale.** -/
theorem etale : Algebra.Etale A C.B :=
  EtSheaves.GalEt.etale (G := C.G) fun m hm => C.unramified m hm.isPrime

/-- Scheme form: `Spec C.B → Spec A` is etale. -/
theorem etale_spec : AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A C.B))) :=
  (AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).2
    (RingHom.etale_algebraMap.2 C.etale)

theorem exists_chr : ∃ (n : ℕ) (x y : Fin n → C.B), EtSheaves.GalEt.CHR C.G x y :=
  EtSheaves.GalEt.exists_chr fun m hm => C.unramified m hm.isPrime

/-- The torsor isomorphism `B ⊗_A B ≅ Π_G B`, `b ⊗ b' ↦ (b σ(b'))_σ`. -/
noncomputable def torsorEquiv : C.B ⊗[A] C.B ≃ₐ[A] (C.G → C.B) :=
  have := Fintype.ofFinite C.G
  EtSheaves.GalEt.torsorEquiv C.exists_chr.choose_spec.choose_spec.choose_spec

theorem torsorEquiv_tmul (b b' : C.B) (σ : C.G) : C.torsorEquiv (b ⊗ₜ[A] b') σ = b * σ • b' := rfl

end RamanujanPetersson.GalCover



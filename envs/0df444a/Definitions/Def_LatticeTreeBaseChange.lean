-- Prove2me | Definitions.Def_LatticeTreeBaseChange
-- name    : LatticeTreeBaseChange
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/aff0a912-8e7a-5fed-8e16-23f3b24e1d05
-- title:
--   Base change and depth balls for the GL₂ lattice tree
-- statement:
--   Working over two pairs $(R',K')$ and $(R,K)$, each a commutative ring together with a field that is an algebra over it, this module introduces a morphism of such pairs and transports the lattice-tree vocabulary of the orbital module along it. `IntegralHom R' K' R K` is a structure with fields a ring homomorphism $K'\to K$, a ring homomorphism $R'\to R$, and the commutation of these with the two algebra maps. For such an $\iota$: `vecMap` applies $\iota$ on $K$-coordinates to vectors in $K'^2$, and is additive, $K'$-semilinear and $R'$-semilinear and compatible with matrix multiplication; `IntegralHom.mapGL` is the induced group homomorphism $\mathrm{GL}_2(K')\to\mathrm{GL}_2(K)$ obtained from Mathlib's entrywise map, compatible with scalar matrices; `latticeBaseChange ι L'` is the $R$-submodule of $K^2$ spanned by the image of $L'$, which turns spans into spans, is monotone, carries the standard lattice into the standard lattice and preserves the predicate `IsFullLattice`; and `Vertex.baseChange` is the induced map on vertices, i.e. on classes of full lattices modulo the homothety relation $L\mapsto \mathrm{scalarGL}(c)\cdot L$, $c\in K^\times$. It intertwines the $\mathrm{GL}_2$-actions through `mapGL`, carries fixed vertices of $g$ to fixed vertices of $\iota(g)$ (whence an inclusion of fixed-vertex sets, and, after conjugating by $P$ with $P^{-1}NP=\iota(\gamma)$, an inclusion into the fixed set of $N$), and every base-changed vertex is fixed by any `IntegralAut` of $(R,K)$ fixing $\iota(K')$ pointwise, so that the twisted action reduces to the untwisted one there. The identity morphism and the morphism underlying an integral automorphism are provided, base change along the identity being the identity on lattices and vertices.
--
--   The second half introduces a depth scale measured by a unit: `LatticeWithin c n L M` asserts $c^nL\le M\le L$, and `Vertex.IsWithin c n v w` asserts that $v,w$ admit representing full lattices in that relation. At $n=0$ these are equality of lattices, resp. of vertices; `IsWithin` is symmetric, monotone in $n$ when multiplication by $c$ shrinks every lattice, and invariant under $\mathrm{GL}_2(K)$ and under an integral automorphism (with $c$ replaced by its image), and base change sends the relation for $c$ to the relation for $\iota(c)$. Finally `orbitalBall c n γ` is the set of vertices $x$ with $x$ and $\gamma\cdot x$ within depth $n$, and `twistedOrbitalBall c n δ σ` the same with the twisted action of $(\delta,\sigma)$; at $n=0$ these are the fixed-vertex set of $\gamma$ and the twisted fixed-vertex set of $(\delta,\sigma)$, the twisted ball for the identity automorphism is the untwisted one, and the ball about the identity matrix is everything when multiplication by $c$ shrinks lattices.
--
--   **Relation to Mathlib.** Mathlib supplies the entrywise map $\mathrm{GL}_2(K')\to\mathrm{GL}_2(K)$ used here, but has no lattice tree for $\mathrm{GL}_2$; the morphisms of pairs, lattice and vertex base change, and the depth relations are the project's own.
--
--   **Where it is used.** This vocabulary underlies the tree-theoretic analysis of elements of $\mathrm{GL}_2$ over a local pair, allowing a configuration over $(R',K')$ to be compared with its image over a larger pair $(R,K)$, and replacing exact fixed points by vertices moved by at most a bounded amount in the scale of a chosen unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LatticeTreeBaseChange.lean

import Definitions.Def_LatticeTreeOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree

attribute [local simp] IntegralAut.symm_toBase IntegralAut.symm_toField galVec_galVec_symm galVec_symm_galVec
  latticeGal_latticeGal_symm latticeGal_symm_latticeGal latticeMap_one mem_fixedVertexSet mem_stdLattice
  mem_twistedFixedVertexSet

section BaseChangeVocabulary

structure IntegralHom (R' K' R K : Type*) [CommRing R'] [Field K'] [Algebra R' K']
    [CommRing R] [Field K] [Algebra R K] where

  toField : K' →+* K

  toBase : R' →+* R

  commutes : ∀ r : R', toField (algebraMap R' K' r) = algebraMap R K (toBase r)

section BaseChange

variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ι : IntegralHom R' K' R K)

def vecMap (v : Fin 2 → K') : Fin 2 → K := fun i => ι.toField (v i)

@[simp] theorem vecMap_apply (v : Fin 2 → K') (i : Fin 2) : vecMap ι v i = ι.toField (v i) := rfl

theorem vecMap_add (v w : Fin 2 → K') : vecMap ι (v + w) = vecMap ι v + vecMap ι w := by
  ext i; simp

theorem vecMap_zero : vecMap ι (0 : Fin 2 → K') = 0 := by
  ext i; simp

theorem vecMap_smul_field (c : K') (v : Fin 2 → K') : vecMap ι (c • v) = ι.toField c • vecMap ι v := by
  ext i; simp

theorem vecMap_smul (r : R') (v : Fin 2 → K') : vecMap ι (r • v) = ι.toBase r • vecMap ι v := by
  ext i
  show ι.toField ((r • v) i) = (ι.toBase r • vecMap ι v) i
  rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul, ι.commutes,
    vecMap_apply]

theorem vecMap_mulVec (M : Matrix (Fin 2) (Fin 2) K') (v : Fin 2 → K') :
    vecMap ι (M *ᵥ v) = M.map ι.toField *ᵥ vecMap ι v := by
  ext i
  exact RingHom.map_mulVec ι.toField M v i

theorem vecMap_single_one (j : Fin 2) : vecMap ι (Pi.single j 1) = Pi.single j 1 := by
  ext i
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [Pi.single_eq_of_ne h]

abbrev IntegralHom.mapGL : Matrix.GeneralLinearGroup (Fin 2) K' →* Matrix.GeneralLinearGroup (Fin 2) K :=
  Matrix.GeneralLinearGroup.map ι.toField

theorem IntegralHom.mapGL_coe (g : Matrix.GeneralLinearGroup (Fin 2) K') :
    ((ι.mapGL g : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (g : Matrix (Fin 2) (Fin 2) K').map ι.toField := by
  ext i j
  exact Matrix.GeneralLinearGroup.map_apply ι.toField i j g

theorem IntegralHom.mapGL_scalarGL (c : K'ˣ) :
    ι.mapGL (scalarGL c) = scalarGL (Units.map (ι.toField : K' →* K) c) := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, scalarGL_coe, scalarGL_coe, Matrix.smul_apply,
    Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, Units.coe_map, MonoidHom.coe_coe]
  congr 1
  rw [Matrix.one_apply, Matrix.one_apply, apply_ite ι.toField, map_one, map_zero]

def latticeBaseChange (L' : Submodule R' (Fin 2 → K')) : Submodule R (Fin 2 → K) :=
  Submodule.span R (vecMap ι '' (L' : Set (Fin 2 → K')))

theorem vecMap_mem_latticeBaseChange {L' : Submodule R' (Fin 2 → K')} {v : Fin 2 → K'}
    (hv : v ∈ L') : vecMap ι v ∈ latticeBaseChange ι L' :=
  Submodule.subset_span ⟨v, hv, rfl⟩

theorem latticeBaseChange_span (s : Set (Fin 2 → K')) :
    latticeBaseChange ι (Submodule.span R' s) = Submodule.span R (vecMap ι '' s) := by
  apply le_antisymm
  · rw [latticeBaseChange, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    induction hw using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [vecMap_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [vecMap_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [vecMap_smul]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem latticeBaseChange_latticeMap (g : Matrix.GeneralLinearGroup (Fin 2) K')
    (L' : Submodule R' (Fin 2 → K')) :
    latticeBaseChange ι (latticeMap g L') = latticeMap (ι.mapGL g) (latticeBaseChange ι L') := by
  have himg : vecMap ι '' (latticeMap g L' : Set (Fin 2 → K'))
      = mulVecLinR (R := R) (ι.mapGL g) '' (vecMap ι '' (L' : Set (Fin 2 → K'))) := by
    ext v
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨vecMap ι w, ⟨w, hw, rfl⟩, ?_⟩
      rw [mulVecLinR_apply, IntegralHom.mapGL_coe, ← vecMap_mulVec]
      rfl
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨(g : Matrix (Fin 2) (Fin 2) K') *ᵥ w, mulVec_mem_latticeMap hw, ?_⟩
      rw [mulVecLinR_apply, IntegralHom.mapGL_coe, ← vecMap_mulVec]
  rw [latticeBaseChange, himg, ← Submodule.map_span]
  rfl

theorem latticeBaseChange_scalarGL (c : K'ˣ) (L' : Submodule R' (Fin 2 → K')) :
    latticeBaseChange ι (latticeMap (scalarGL c) L')
      = latticeMap (scalarGL (Units.map (ι.toField : K' →* K) c)) (latticeBaseChange ι L') := by
  rw [latticeBaseChange_latticeMap, IntegralHom.mapGL_scalarGL]

theorem IsFullLattice.baseChange {L' : Submodule R' (Fin 2 → K')} (hL' : IsFullLattice L') :
    IsFullLattice (latticeBaseChange ι L') := by
  refine ⟨?_, ?_⟩
  · obtain ⟨s, hs⟩ := hL'.1
    rw [← hs, latticeBaseChange_span]
    exact Submodule.fg_span (s.finite_toSet.image _)
  · rw [eq_top_iff]
    intro v _
    have hbasis : ∀ j : Fin 2, (Pi.single j 1 : Fin 2 → K)
        ∈ Submodule.span K ((latticeBaseChange ι L' : Set (Fin 2 → K))) := by
      intro j
      have key : ∀ x ∈ Submodule.span K' ((L' : Set (Fin 2 → K'))),
          vecMap ι x ∈ Submodule.span K ((latticeBaseChange ι L' : Set (Fin 2 → K))) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx => exact Submodule.subset_span (vecMap_mem_latticeBaseChange ι hx)
        | zero => rw [vecMap_zero]; exact Submodule.zero_mem _
        | add x y _ _ hx hy => rw [vecMap_add]; exact Submodule.add_mem _ hx hy
        | smul c x _ hx => rw [vecMap_smul_field]; exact Submodule.smul_mem _ _ hx
      rw [← vecMap_single_one ι j]
      exact key _ (hL'.2 ▸ Submodule.mem_top)
    have hv : v = v 0 • (Pi.single 0 1 : Fin 2 → K) + v 1 • (Pi.single 1 1 : Fin 2 → K) := by
      ext i
      fin_cases i <;> simp
    rw [hv]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hbasis 0)) (Submodule.smul_mem _ _ (hbasis 1))

def Vertex.baseChange : Vertex R' K' → Vertex R K :=
  Quotient.map (fun L => ⟨latticeBaseChange ι L.1, L.2.baseChange ι⟩)
    (by
      rintro ⟨L, hL⟩ ⟨L', hL'⟩ ⟨c, hc⟩
      refine ⟨Units.map (ι.toField : K' →* K) c, ?_⟩
      show latticeMap _ (latticeBaseChange ι L) = latticeBaseChange ι L'
      rw [← latticeBaseChange_scalarGL, hc])

@[simp] theorem Vertex.baseChange_mk (L' : Submodule R' (Fin 2 → K')) (hL' : IsFullLattice L') :
    Vertex.baseChange ι (Vertex.mk R' K' L' hL')
      = Vertex.mk R K (latticeBaseChange ι L') (hL'.baseChange ι) :=
  rfl

theorem Vertex.baseChange_act (g : Matrix.GeneralLinearGroup (Fin 2) K') (v : Vertex R' K') :
    Vertex.baseChange ι (Vertex.act g v) = Vertex.act (ι.mapGL g) (Vertex.baseChange ι v) := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (latticeBaseChange_latticeMap ι g L.1))

theorem latticeBaseChange_stdLattice_le : latticeBaseChange ι (stdLattice R' K') ≤ stdLattice R K := by
  rw [latticeBaseChange, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩ i
  obtain ⟨r, hr⟩ := hw i
  exact ⟨ι.toBase r, by rw [vecMap_apply, ← hr, ι.commutes]⟩

theorem IsFixedVertex.baseChange {g : Matrix.GeneralLinearGroup (Fin 2) K'} {v : Vertex R' K'}
    (hv : IsFixedVertex g v) : IsFixedVertex (ι.mapGL g) (Vertex.baseChange ι v) := by
  rw [IsFixedVertex, ← Vertex.baseChange_act, hv]

theorem baseChange_image_fixedVertexSet_subset (g : Matrix.GeneralLinearGroup (Fin 2) K') :
    Vertex.baseChange ι '' fixedVertexSet (R := R') g ⊆ fixedVertexSet (R := R) (ι.mapGL g) := by
  rintro _ ⟨v, hv, rfl⟩
  exact IsFixedVertex.baseChange ι hv

theorem act_mem_fixedVertexSet_conj {g P : Matrix.GeneralLinearGroup (Fin 2) K} {v : Vertex R K}
    (hv : IsFixedVertex g v) : IsFixedVertex (P * g * P⁻¹) (Vertex.act P v) := by
  rw [IsFixedVertex, ← Vertex.act_mul, inv_mul_cancel_right, Vertex.act_mul, hv]

theorem act_baseChange_fixed_subset_of_conj_eq {N P : Matrix.GeneralLinearGroup (Fin 2) K}
    {γ : Matrix.GeneralLinearGroup (Fin 2) K'} (hP : P⁻¹ * N * P = ι.mapGL γ) :
    Vertex.act P '' (Vertex.baseChange ι '' fixedVertexSet (R := R') γ)
      ⊆ fixedVertexSet (R := R) N := by
  rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  have h := act_mem_fixedVertexSet_conj (P := P) (IsFixedVertex.baseChange ι hv)
  rwa [← hP, show P * (P⁻¹ * N * P) * P⁻¹ = N by group] at h

theorem latticeGal_latticeBaseChange {σ : IntegralAut R K}
    (hσ : ∀ x : K', σ.toField (ι.toField x) = ι.toField x) (L' : Submodule R' (Fin 2 → K')) :
    latticeGal σ (latticeBaseChange ι L') = latticeBaseChange ι L' := by
  have hfix : galVec σ '' (vecMap ι '' (L' : Set (Fin 2 → K'))) = vecMap ι '' (L' : Set (Fin 2 → K')) := by
    have hpt : ∀ w : Fin 2 → K', galVec σ (vecMap ι w) = vecMap ι w := fun w => by
      ext i; simp [hσ]
    ext v
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, (hpt w).symm⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨vecMap ι w, ⟨w, hw, rfl⟩, hpt w⟩
  rw [latticeBaseChange, latticeGal_span, hfix]

theorem Vertex.galAct_baseChange {σ : IntegralAut R K}
    (hσ : ∀ x : K', σ.toField (ι.toField x) = ι.toField x) (v : Vertex R' K') :
    Vertex.galAct σ (Vertex.baseChange ι v) = Vertex.baseChange ι v := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (latticeGal_latticeBaseChange ι hσ L.1))

theorem Vertex.twistedAct_baseChange {σ : IntegralAut R K}
    (hσ : ∀ x : K', σ.toField (ι.toField x) = ι.toField x)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R' K') :
    Vertex.twistedAct g σ (Vertex.baseChange ι v) = Vertex.act g (Vertex.baseChange ι v) := by
  rw [Vertex.twistedAct, Vertex.galAct_baseChange ι hσ]

end BaseChange

section Inhabitants

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

variable (R K) in

def IntegralHom.refl : IntegralHom R K R K where
  toField := RingHom.id K
  toBase := RingHom.id R
  commutes _ := rfl

def IntegralAut.toIntegralHom (σ : IntegralAut R K) : IntegralHom R K R K where
  toField := σ.toField
  toBase := σ.toBase
  commutes := σ.commutes

@[simp] theorem vecMap_refl (v : Fin 2 → K) : vecMap (IntegralHom.refl R K) v = v := rfl

theorem latticeBaseChange_refl (L : Submodule R (Fin 2 → K)) :
    latticeBaseChange (IntegralHom.refl R K) L = L := by
  have h : vecMap (IntegralHom.refl R K) '' (L : Set (Fin 2 → K)) = L := by
    ext v; simp
  rw [latticeBaseChange, h, Submodule.span_eq]

theorem Vertex.baseChange_refl (v : Vertex R K) : Vertex.baseChange (IntegralHom.refl R K) v = v := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (latticeBaseChange_refl L.1))

theorem nonempty_vertex : Nonempty (Vertex R K) := ⟨stdVertex R K⟩

end Inhabitants

section Monotone

variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ι : IntegralHom R' K' R K)

theorem latticeBaseChange_mono {L₁ L₂ : Submodule R' (Fin 2 → K')} (h : L₁ ≤ L₂) :
    latticeBaseChange ι L₁ ≤ latticeBaseChange ι L₂ :=
  Submodule.span_mono (Set.image_mono h)

theorem latticeGal_mono (σ : IntegralAut R K) {L₁ L₂ : Submodule R (Fin 2 → K)} (h : L₁ ≤ L₂) :
    latticeGal σ L₁ ≤ latticeGal σ L₂ := by
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w, h hw, rfl⟩

end Monotone

section DepthCurrency

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

def LatticeWithin (c : Kˣ) (n : ℕ) (L M : Submodule R (Fin 2 → K)) : Prop :=
  latticeMap (scalarGL (c ^ n)) L ≤ M ∧ M ≤ L

def Vertex.IsWithin (c : Kˣ) (n : ℕ) (v w : Vertex R K) : Prop :=
  ∃ (L M : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) (hM : IsFullLattice M),
    Vertex.mk R K L hL = v ∧ Vertex.mk R K M hM = w ∧ LatticeWithin c n L M

theorem latticeWithin_zero_iff (c : Kˣ) (L M : Submodule R (Fin 2 → K)) :
    LatticeWithin c 0 L M ↔ M = L := by
  simp only [LatticeWithin, pow_zero, scalarGL_one, latticeMap_one]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

theorem Vertex.isWithin_zero_iff (c : Kˣ) (v w : Vertex R K) : Vertex.IsWithin c 0 v w ↔ v = w := by
  constructor
  · rintro ⟨L, M, hL, hM, rfl, rfl, h⟩
    rw [latticeWithin_zero_iff] at h
    subst h
    rfl
  · rintro rfl
    induction v using Quotient.inductionOn with
    | h L => exact ⟨L.1, L.1, L.2, L.2, rfl, rfl, (latticeWithin_zero_iff c _ _).mpr rfl⟩

theorem LatticeWithin.symm_rescale {c : Kˣ} {n : ℕ} {L M : Submodule R (Fin 2 → K)}
    (h : LatticeWithin c n L M) :
    LatticeWithin c n (latticeMap (scalarGL (c ^ n))⁻¹ M) L := by
  obtain ⟨hlow, hup⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← latticeMap_mul, mul_inv_cancel, latticeMap_one]
    exact hup
  · have := latticeMap_mono (scalarGL (c ^ n))⁻¹ hlow
    rwa [latticeMap_inv_latticeMap] at this

theorem Vertex.IsWithin.symm {c : Kˣ} {n : ℕ} {v w : Vertex R K} (h : Vertex.IsWithin c n v w) :
    Vertex.IsWithin c n w v := by
  obtain ⟨L, M, hL, hM, rfl, rfl, hLM⟩ := h
  refine ⟨latticeMap (scalarGL (c ^ n))⁻¹ M, L, hM.map _, hL, ?_, rfl, hLM.symm_rescale⟩
  rw [Vertex.mk_eq_mk_iff]
  exact ⟨c ^ n, by rw [← latticeMap_mul, mul_inv_cancel, latticeMap_one]⟩

theorem Vertex.isWithin_comm (c : Kˣ) (n : ℕ) (v w : Vertex R K) :
    Vertex.IsWithin c n v w ↔ Vertex.IsWithin c n w v :=
  ⟨Vertex.IsWithin.symm, Vertex.IsWithin.symm⟩

theorem latticeMap_scalarGL_pow_le_of_le {c : Kˣ}
    (hc : ∀ L : Submodule R (Fin 2 → K), latticeMap (scalarGL c) L ≤ L) (k : ℕ) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL (c ^ k)) L ≤ L := by
  induction k with
  | zero => rw [pow_zero, scalarGL_one, latticeMap_one]
  | succ k ih =>
      rw [pow_succ, scalarGL_mul, latticeMap_mul]
      exact le_trans (latticeMap_mono _ (hc L)) ih

theorem LatticeWithin.mono {c : Kˣ} (hc : ∀ L : Submodule R (Fin 2 → K), latticeMap (scalarGL c) L ≤ L)
    {m n : ℕ} (hmn : m ≤ n) {L M : Submodule R (Fin 2 → K)} (h : LatticeWithin c m L M) :
    LatticeWithin c n L M := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  refine ⟨le_trans ?_ h.1, h.2⟩
  rw [pow_add, scalarGL_mul, latticeMap_mul]
  exact latticeMap_mono _ (latticeMap_scalarGL_pow_le_of_le hc k L)

theorem Vertex.IsWithin.mono {c : Kˣ} (hc : ∀ L : Submodule R (Fin 2 → K), latticeMap (scalarGL c) L ≤ L)
    {m n : ℕ} (hmn : m ≤ n) {v w : Vertex R K} (h : Vertex.IsWithin c m v w) : Vertex.IsWithin c n v w := by
  obtain ⟨L, M, hL, hM, rfl, rfl, hLM⟩ := h
  exact ⟨L, M, hL, hM, rfl, rfl, hLM.mono hc hmn⟩

theorem latticeWithin_latticeMap_iff (c : Kˣ) (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (L M : Submodule R (Fin 2 → K)) :
    LatticeWithin c n (latticeMap g L) (latticeMap g M) ↔ LatticeWithin c n L M := by
  unfold LatticeWithin
  rw [← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · simpa only [latticeMap_inv_latticeMap] using latticeMap_mono g⁻¹ h1
    · simpa only [latticeMap_inv_latticeMap] using latticeMap_mono g⁻¹ h2
  · rintro ⟨h1, h2⟩
    exact ⟨latticeMap_mono g h1, latticeMap_mono g h2⟩

theorem latticeWithin_latticeGal_iff (σ : IntegralAut R K) (c : Kˣ) (n : ℕ) (L M : Submodule R (Fin 2 → K)) :
    LatticeWithin (σ.unitMap c) n (latticeGal σ L) (latticeGal σ M) ↔ LatticeWithin c n L M := by
  have hpow : σ.unitMap c ^ n = σ.unitMap (c ^ n) := by
    ext
    simp only [Units.val_pow_eq_pow_val, IntegralAut.unitMap_coe, map_pow]
  unfold LatticeWithin
  rw [hpow, ← latticeGal_scalarGL]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · simpa only [latticeGal_symm_latticeGal] using latticeGal_mono σ.symm h1
    · simpa only [latticeGal_symm_latticeGal] using latticeGal_mono σ.symm h2
  · rintro ⟨h1, h2⟩
    exact ⟨latticeGal_mono σ h1, latticeGal_mono σ h2⟩

end DepthCurrency

section DepthBaseChange

variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ι : IntegralHom R' K' R K)

theorem LatticeWithin.baseChange {c : K'ˣ} {n : ℕ} {L M : Submodule R' (Fin 2 → K')}
    (h : LatticeWithin c n L M) :
    LatticeWithin (Units.map (ι.toField : K' →* K) c) n (latticeBaseChange ι L) (latticeBaseChange ι M) := by
  refine ⟨?_, latticeBaseChange_mono ι h.2⟩
  have := latticeBaseChange_mono ι h.1
  rwa [latticeBaseChange_scalarGL, map_pow] at this

theorem Vertex.IsWithin.baseChange {c : K'ˣ} {n : ℕ} {v w : Vertex R' K'} (h : Vertex.IsWithin c n v w) :
    Vertex.IsWithin (Units.map (ι.toField : K' →* K) c) n
      (Vertex.baseChange ι v) (Vertex.baseChange ι w) := by
  obtain ⟨L, M, hL, hM, rfl, rfl, hLM⟩ := h
  exact ⟨latticeBaseChange ι L, latticeBaseChange ι M, hL.baseChange ι, hM.baseChange ι, rfl, rfl,
    hLM.baseChange ι⟩

end DepthBaseChange

section DepthOrbital

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

def orbitalBall (c : Kˣ) (n : ℕ) (γ : Matrix.GeneralLinearGroup (Fin 2) K) : Set (Vertex R K) :=
  {x | Vertex.IsWithin c n x (Vertex.act γ x)}

def twistedOrbitalBall (c : Kˣ) (n : ℕ) (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) :
    Set (Vertex R K) :=
  {x | Vertex.IsWithin c n x (Vertex.twistedAct δ σ x)}

theorem mem_orbitalBall {c : Kˣ} {n : ℕ} {γ : Matrix.GeneralLinearGroup (Fin 2) K}
    {x : Vertex R K} : x ∈ orbitalBall (R := R) c n γ ↔ Vertex.IsWithin c n x (Vertex.act γ x) :=
  Iff.rfl

theorem mem_twistedOrbitalBall {c : Kˣ} {n : ℕ} {δ : Matrix.GeneralLinearGroup (Fin 2) K}
    {σ : IntegralAut R K} {x : Vertex R K} :
    x ∈ twistedOrbitalBall c n δ σ ↔ Vertex.IsWithin c n x (Vertex.twistedAct δ σ x) :=
  Iff.rfl

attribute [local simp] mem_orbitalBall mem_twistedOrbitalBall

theorem orbitalBall_zero (c : Kˣ) (γ : Matrix.GeneralLinearGroup (Fin 2) K) :
    orbitalBall (R := R) c 0 γ = fixedVertexSet γ := by
  ext x
  rw [mem_orbitalBall, Vertex.isWithin_zero_iff, mem_fixedVertexSet, eq_comm]

theorem twistedOrbitalBall_zero (c : Kˣ) (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) :
    twistedOrbitalBall c 0 δ σ = twistedFixedVertexSet δ σ := by
  ext x
  rw [mem_twistedOrbitalBall, Vertex.isWithin_zero_iff, mem_twistedFixedVertexSet, eq_comm]

theorem twistedOrbitalBall_refl (c : Kˣ) (n : ℕ) (δ : Matrix.GeneralLinearGroup (Fin 2) K) :
    twistedOrbitalBall c n δ (IntegralAut.refl R K) = orbitalBall c n δ := by
  ext x
  rw [mem_twistedOrbitalBall, mem_orbitalBall, Vertex.twistedAct, Vertex.galAct_refl]

theorem orbitalBall_one {c : Kˣ} (hc : ∀ L : Submodule R (Fin 2 → K), latticeMap (scalarGL c) L ≤ L)
    (n : ℕ) : orbitalBall (R := R) c n 1 = Set.univ := by
  ext x
  simp only [mem_orbitalBall, Vertex.act_one, Set.mem_univ, iff_true]
  exact ((Vertex.isWithin_zero_iff c x x).mpr rfl).mono hc (Nat.zero_le n)

end DepthOrbital

end BaseChangeVocabulary

end LT.LatticeTree



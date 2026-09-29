-- Prove2me | Definitions.Def_AlgebraicCurve_LogDeRhamH1
-- name    : AlgebraicCurve_LogDeRhamH1
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/02c50aa3-eafc-52ce-8883-7c645cb05a80
-- title:
--   Logarithmic de Rham cohomology of a curve in pair presentation
-- statement:
--   For fields $K \subseteq F$ with $F$ a $K$-algebra and $S$ a set of places $v$ of $F/K$ (a place being a proper valuation subring of $F$ containing $K$ whose ideals are principal, so a discrete valuation ring, with $d\pi_v$ its distinguished differential `dCoord`), the module fixes a uniformiser $\pi_v$ realising `dCoord` and defines the local predicates: `HasPoleOrderLE n ω` holds when $\omega = f\,d\pi_v$ for some $f \in F$ with $\pi_v^n f$ in the valuation ring; `FnPoleOrderLE n g` says $\pi_v^n g$ lies in the valuation ring; and `HasLogResidue ω a`, for $a \in K$, says $\omega = f\,d\pi_v$ with $\pi_v f$ integral at $v$ and of residue the image of $a$. Routine lemmas record additivity, $K$-semilinearity and monotonicity in $n$, and that a logarithmic residue forces pole order at most $1$. The $K$-submodule `logForms K F S` of $\Omega_{F/K}$ consists of forms of pole order $\le 0$ off $S$ and $\le 1$ on $S$; it contains `regularDifferentials`.
--
--   The cohomology is defined on the pair model: `cocycles` is the $K$-submodule of $(\omega,g) \in \Omega_{F/K} \times F$ with $\omega$ of pole order $\le 0$ at every $v \notin S$ and $\omega - dg$ of pole order $\le 1$ at every $v \in S$ — no bound whatever is imposed on the poles of $g$; `coboundaries` is the sum of `exactPart`, the pairs $(dh,h)$ with $h$ integral off $S$, and `localPart`, the pairs $(0,r)$ with $r$ integral on $S$; `H1 K F S` is the quotient of `cocycles` by the induced submodule, with quotient map `mk`. Alongside sit `regularOff`, `regularOn` and `H1O K F S = F/(\text{regularOff} + \text{regularOn})`, the maps `ofLog` and `ofRegular` sending $\omega$ to the class of $(\omega,0)$, and `toH1O` induced by the second projection.
--
--   Further notions on classes: `HasResidueAt S v x a` is the relation that some cocycle representing $x$ has $\omega - dg$ with logarithmic residue $a$ at $v$; `IsSecondKind x` requires residue $0$ at every $v \in S$; `IsClassOfWithTail m ω x` says $x$ is the class of a cocycle $(\omega,g)$ whose $g$ has pole order $\le m$ at every $v \in S$. Functoriality is given by `pullbackForm`/`pullbackPair` along a $K$-algebra map $\varphi : F \to F'$ (restriction of scalars of the map on Kähler differentials), and `H1.map`, which takes as explicit hypotheses that $\varphi$ carries cocycles to cocycles and coboundaries to coboundaries. In characteristic $p$, $d(g^p)=0$ yields `frobPair` $(\omega,g) \mapsto (0,g^p)$ and the Frobenius-semilinear operator `H1.frob`. Finally `CartierHypotheses p C` is a structure packaging, for an additive endomorphism $C$ of $\Omega_{F/K}$, that $C$ is semilinear for the inverse of Frobenius on $K$, kills exact forms, and preserves pole order $\le 0$ and $\le 1$ at every place; from such a $C$, `cartierPair` $(\omega,g) \mapsto (C\omega,0)$ induces the semilinear operator `H1.cartier`.
--
--   **Relation to Mathlib.** Mathlib supplies the module of Kähler differentials $\Omega_{F/K}$, its functoriality (`KaehlerDifferential.map`, used for `pullbackForm`) and the Frobenius ring maps; the notion of place used here and the whole logarithmic de Rham complex in this pair presentation, including the Cartier-type operator axioms, are the project's own.
--
--   **Where it is used.** The space $H^1$ defined here, with its Frobenius and Cartier-type operators, residues along $S$ and classes of the second kind, is the carrier in which differentials on curves in characteristic $p$ with prescribed poles along a finite set of places (for instance supersingular points on an Igusa curve) are studied, the `IsClassOfWithTail` relation recording the correcting function that turns such a differential into a cohomology class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_LogDeRhamH1.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

private def unifLDR : F :=
  ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F)

private theorem unifLDR_mem : v.unifLDR ∈ v.toValuationSubring :=
  SetLike.coe_mem (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose

private theorem dCoord_eq_D_unifLDR : v.dCoord = D K F v.unifLDR := rfl

def HasPoleOrderLE (n : ℕ) (ω : Ω[F⁄K]) : Prop :=
  ∃ f : F, v.unifLDR ^ n * f ∈ v.toValuationSubring ∧ ω = f • v.dCoord

def FnPoleOrderLE (n : ℕ) (g : F) : Prop :=
  v.unifLDR ^ n * g ∈ v.toValuationSubring

def HasLogResidue (ω : Ω[F⁄K]) (a : K) : Prop :=
  ∃ f : F, ω = f • v.dCoord ∧ v.HasValue (v.unifLDR * f) a

variable {v}

variable (v) in
theorem hasPoleOrderLE_zero_right (n : ℕ) : v.HasPoleOrderLE n (0 : Ω[F⁄K]) :=
  ⟨0, by rw [mul_zero]; exact zero_mem _, by rw [zero_smul]⟩

theorem HasPoleOrderLE.add {n : ℕ} {ω η : Ω[F⁄K]} (hω : v.HasPoleOrderLE n ω)
    (hη : v.HasPoleOrderLE n η) : v.HasPoleOrderLE n (ω + η) := by
  obtain ⟨f, hf, rfl⟩ := hω
  obtain ⟨g, hg, rfl⟩ := hη
  exact ⟨f + g, by rw [mul_add]; exact add_mem hf hg, by rw [add_smul]⟩

theorem HasPoleOrderLE.neg {n : ℕ} {ω : Ω[F⁄K]} (hω : v.HasPoleOrderLE n ω) :
    v.HasPoleOrderLE n (-ω) := by
  obtain ⟨f, hf, rfl⟩ := hω
  exact ⟨-f, by rw [mul_neg]; exact neg_mem hf, by rw [neg_smul]⟩

theorem HasPoleOrderLE.sub {n : ℕ} {ω η : Ω[F⁄K]} (hω : v.HasPoleOrderLE n ω)
    (hη : v.HasPoleOrderLE n η) : v.HasPoleOrderLE n (ω - η) := by
  rw [sub_eq_add_neg]; exact hω.add hη.neg

theorem HasPoleOrderLE.smul {n : ℕ} (c : K) {ω : Ω[F⁄K]} (hω : v.HasPoleOrderLE n ω) :
    v.HasPoleOrderLE n (c • ω) := by
  obtain ⟨f, hf, rfl⟩ := hω
  refine ⟨algebraMap K F c * f, ?_, by rw [mul_smul, algebraMap_smul]⟩
  rw [mul_left_comm]
  exact mul_mem (v.algebraMap_mem' c) hf

theorem HasPoleOrderLE.of_le {m n : ℕ} (h : m ≤ n) {ω : Ω[F⁄K]} (hω : v.HasPoleOrderLE m ω) :
    v.HasPoleOrderLE n ω := by
  obtain ⟨f, hf, rfl⟩ := hω
  refine ⟨f, ?_, rfl⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm, pow_add, mul_assoc]
  exact mul_mem (pow_mem v.unifLDR_mem k) hf

theorem hasPoleOrderLE_zero_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.HasPoleOrderLE 0 (f • v.dCoord) :=
  ⟨f, by rw [pow_zero, one_mul]; exact hf, rfl⟩

theorem FnPoleOrderLE.add {n : ℕ} {g h : F} (hg : v.FnPoleOrderLE n g) (hh : v.FnPoleOrderLE n h) :
    v.FnPoleOrderLE n (g + h) := by
  unfold FnPoleOrderLE at *
  rw [mul_add]; exact add_mem hg hh

theorem FnPoleOrderLE.smul {n : ℕ} (c : K) {g : F} (hg : v.FnPoleOrderLE n g) :
    v.FnPoleOrderLE n (algebraMap K F c * g) := by
  unfold FnPoleOrderLE at *
  rw [mul_left_comm]; exact mul_mem (v.algebraMap_mem' c) hg

theorem fnPoleOrderLE_zero_iff (g : F) : v.FnPoleOrderLE 0 g ↔ g ∈ v.toValuationSubring := by
  unfold FnPoleOrderLE; rw [pow_zero, one_mul]

theorem HasLogResidue.hasPoleOrderLE {ω : Ω[F⁄K]} {a : K} (h : v.HasLogResidue ω a) :
    v.HasPoleOrderLE 1 ω := by
  obtain ⟨f, rfl, hval⟩ := h
  exact ⟨f, by rw [pow_one]; exact hval.mem, rfl⟩

end Place

section LogForms

variable (K F)

def logForms (S : Set (Place K F)) : Submodule K Ω[F⁄K] where
  carrier := {ω | ∀ v : Place K F, (v ∉ S → v.HasPoleOrderLE 0 ω) ∧ (v ∈ S → v.HasPoleOrderLE 1 ω)}
  zero_mem' v := ⟨fun _ => v.hasPoleOrderLE_zero_right 0, fun _ => v.hasPoleOrderLE_zero_right 1⟩
  add_mem' hω hη v :=
    ⟨fun hv => ((hω v).1 hv).add ((hη v).1 hv), fun hv => ((hω v).2 hv).add ((hη v).2 hv)⟩
  smul_mem' c _ hω v := ⟨fun hv => ((hω v).1 hv).smul c, fun hv => ((hω v).2 hv).smul c⟩

variable {K F}

theorem mem_logForms_iff {S : Set (Place K F)} {ω : Ω[F⁄K]} :
    ω ∈ logForms K F S ↔
      ∀ v : Place K F, (v ∉ S → v.HasPoleOrderLE 0 ω) ∧ (v ∈ S → v.HasPoleOrderLE 1 ω) :=
  Iff.rfl

theorem regularDifferentials_le_logForms (S : Set (Place K F)) :
    regularDifferentials K F ≤ logForms K F S := by
  intro ω hω v
  obtain ⟨f, hf, hωf⟩ := hω v
  have h0 : v.HasPoleOrderLE 0 ω := by rw [hωf]; exact Place.hasPoleOrderLE_zero_of_mem hf
  exact ⟨fun _ => h0, fun _ => h0.of_le (Nat.zero_le 1)⟩

end LogForms

namespace LogDeRham

variable (K F)

def cocycles (S : Set (Place K F)) : Submodule K (Ω[F⁄K] × F) where
  carrier := {c | (∀ v : Place K F, v ∉ S → v.HasPoleOrderLE 0 c.1) ∧
    (∀ v : Place K F, v ∈ S → v.HasPoleOrderLE 1 (c.1 - D K F c.2))}
  zero_mem' := by
    refine ⟨fun v _ => ?_, fun v _ => ?_⟩
    · exact v.hasPoleOrderLE_zero_right 0
    · show v.HasPoleOrderLE 1 ((0 : Ω[F⁄K]) - D K F (0 : F))
      rw [map_zero, sub_zero]; exact v.hasPoleOrderLE_zero_right 1
  add_mem' {c c'} hc hc' := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · show v.HasPoleOrderLE 0 (c.1 + c'.1)
      exact (hc.1 v hv).add (hc'.1 v hv)
    · have h := (hc.2 v hv).add (hc'.2 v hv)
      show v.HasPoleOrderLE 1 ((c.1 + c'.1) - D K F (c.2 + c'.2))
      rw [map_add]
      convert h using 1
      abel
  smul_mem' a {c} hc := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · show v.HasPoleOrderLE 0 (a • c.1)
      exact (hc.1 v hv).smul a
    · have h := (hc.2 v hv).smul a
      rw [smul_sub] at h
      show v.HasPoleOrderLE 1 (a • c.1 - D K F (a • c.2))

      have hD : D K F (a • c.2) = a • D K F c.2 := by
        rw [Algebra.smul_def, Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero,
          ← algebraMap_smul F a (D K F c.2)]
      rw [hD]; exact h

def exactPart (S : Set (Place K F)) : Submodule K (Ω[F⁄K] × F) where
  carrier := {c | ∃ h : F, (∀ v : Place K F, v ∉ S → h ∈ v.toValuationSubring) ∧ c = (D K F h, h)}
  zero_mem' := ⟨0, fun v _ => zero_mem _, Prod.ext (by simp) rfl⟩
  add_mem' := by
    rintro _ _ ⟨h, hh, rfl⟩ ⟨h', hh', rfl⟩
    exact ⟨h + h', fun v hv => add_mem (hh v hv) (hh' v hv), Prod.ext (by simp [map_add]) rfl⟩
  smul_mem' := by
    rintro a _ ⟨h, hh, rfl⟩
    refine ⟨a • h, fun v hv => ?_, ?_⟩
    · rw [Algebra.smul_def]; exact mul_mem (v.algebraMap_mem' a) (hh v hv)
    · have hD : D K F (a • h) = a • D K F h := by
        rw [Algebra.smul_def, Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero,
          ← algebraMap_smul F a (D K F h)]
      exact Prod.ext (by rw [Prod.smul_mk, hD]) (by rw [Prod.smul_mk])

def localPart (S : Set (Place K F)) : Submodule K (Ω[F⁄K] × F) where
  carrier := {c | c.1 = 0 ∧ ∀ v : Place K F, v ∈ S → c.2 ∈ v.toValuationSubring}
  zero_mem' := ⟨rfl, fun v _ => zero_mem _⟩
  add_mem' {c c'} hc hc' := ⟨by rw [Prod.fst_add, hc.1, hc'.1, add_zero],
    fun v hv => add_mem (hc.2 v hv) (hc'.2 v hv)⟩
  smul_mem' a {c} hc := ⟨by rw [Prod.smul_fst, hc.1, smul_zero], fun v hv => by
    rw [Prod.smul_snd, Algebra.smul_def]; exact mul_mem (v.algebraMap_mem' a) (hc.2 v hv)⟩

def coboundaries (S : Set (Place K F)) : Submodule K (Ω[F⁄K] × F) :=
  exactPart K F S ⊔ localPart K F S

abbrev coboundariesIn (S : Set (Place K F)) : Submodule K ↥(cocycles K F S) :=
  (coboundaries K F S).comap (cocycles K F S).subtype

abbrev H1 (S : Set (Place K F)) : Type _ :=
  ↥(cocycles K F S) ⧸ coboundariesIn K F S

def regularOff (S : Set (Place K F)) : Submodule K F where
  carrier := {h | ∀ v : Place K F, v ∉ S → h ∈ v.toValuationSubring}
  zero_mem' v _ := zero_mem _
  add_mem' {h h'} hh hh' v hv := add_mem (hh v hv) (hh' v hv)
  smul_mem' a {h} hh v hv := by rw [Algebra.smul_def]; exact mul_mem (v.algebraMap_mem' a) (hh v hv)

def regularOn (S : Set (Place K F)) : Submodule K F where
  carrier := {r | ∀ v : Place K F, v ∈ S → r ∈ v.toValuationSubring}
  zero_mem' v _ := zero_mem _
  add_mem' {h h'} hh hh' v hv := add_mem (hh v hv) (hh' v hv)
  smul_mem' a {h} hh v hv := by rw [Algebra.smul_def]; exact mul_mem (v.algebraMap_mem' a) (hh v hv)

abbrev H1O (S : Set (Place K F)) : Type _ :=
  F ⧸ (regularOff K F S ⊔ regularOn K F S)

namespace H1

variable {K F}
variable (S : Set (Place K F))

def mk : ↥(cocycles K F S) →ₗ[K] H1 K F S := (coboundariesIn K F S).mkQ

theorem inl_mem_cocycles {ω : Ω[F⁄K]} (hω : ω ∈ logForms K F S) : (ω, (0 : F)) ∈ cocycles K F S := by
  refine ⟨fun v hv => (hω v).1 hv, fun v hv => ?_⟩
  rw [map_zero, sub_zero]
  exact (hω v).2 hv

def ofLog : ↥(logForms K F S) →ₗ[K] H1 K F S :=
  (mk S).comp
    (LinearMap.codRestrict (cocycles K F S) ((LinearMap.inl K Ω[F⁄K] F).domRestrict (logForms K F S))
      (fun ω => inl_mem_cocycles S ω.2))

def ofRegular : ↥(regularDifferentials K F) →ₗ[K] H1 K F S :=
  (ofLog S).comp (Submodule.inclusion (regularDifferentials_le_logForms S))

theorem snd_mem_of_mem_coboundaries {c : Ω[F⁄K] × F} (hc : c ∈ coboundaries K F S) :
    c.2 ∈ regularOff K F S ⊔ regularOn K F S := by
  have hc' : c ∈ exactPart K F S ⊔ localPart K F S := hc
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hc'
  obtain ⟨h, hh, rfl⟩ := hy
  rw [Prod.snd_add]
  exact add_mem (Submodule.mem_sup_left hh) (Submodule.mem_sup_right (hz.2))

def toH1O : H1 K F S →ₗ[K] H1O K F S :=
  (coboundariesIn K F S).liftQ
    ((regularOff K F S ⊔ regularOn K F S).mkQ.comp
      ((LinearMap.snd K Ω[F⁄K] F).comp (cocycles K F S).subtype))
    (by
      intro c hc
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact snd_mem_of_mem_coboundaries S hc)

def HasResidueAt (v : Place K F) (x : H1 K F S) (a : K) : Prop :=
  ∃ c : ↥(cocycles K F S), mk S c = x ∧ v.HasLogResidue ((c : Ω[F⁄K] × F).1 - D K F (c : Ω[F⁄K] × F).2) a

def IsSecondKind (x : H1 K F S) : Prop :=
  ∀ v : Place K F, v ∈ S → HasResidueAt S v x 0

def IsClassOfWithTail (m : ℕ) (ω : Ω[F⁄K]) (x : H1 K F S) : Prop :=
  ∃ g : F, (∀ v : Place K F, v ∈ S → v.FnPoleOrderLE m g) ∧
    ∃ hc : (ω, g) ∈ cocycles K F S, mk S ⟨(ω, g), hc⟩ = x

end H1

section Map

variable {K F}
variable {F' : Type*} [Field F'] [Algebra K F']

def pullbackForm (φ : F →ₐ[K] F') : Ω[F⁄K] →ₗ[K] Ω[F'⁄K] :=
  letI : Algebra F F' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  (KaehlerDifferential.map K K F F').restrictScalars K

theorem pullbackForm_D (φ : F →ₐ[K] F') (x : F) :
    pullbackForm φ (D K F x) = D K F' (φ x) := by
  letI : Algebra F F' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  exact KaehlerDifferential.map_D K K F F' x

def pullbackPair (φ : F →ₐ[K] F') : (Ω[F⁄K] × F) →ₗ[K] (Ω[F'⁄K] × F') :=
  (pullbackForm φ).prodMap φ.toLinearMap

@[simp] theorem pullbackPair_apply (φ : F →ₐ[K] F') (c : Ω[F⁄K] × F) :
    pullbackPair φ c = (pullbackForm φ c.1, φ c.2) := rfl

theorem pullbackPair_D (φ : F →ₐ[K] F') (h : F) :
    pullbackPair φ (D K F h, h) = (D K F' (φ h), φ h) := by
  rw [pullbackPair_apply, pullbackForm_D]

def H1.map (S : Set (Place K F)) (T : Set (Place K F')) (φ : F →ₐ[K] F')
    (hZ : ∀ c ∈ cocycles K F S, pullbackPair φ c ∈ cocycles K F' T)
    (hB : ∀ c ∈ coboundaries K F S, pullbackPair φ c ∈ coboundaries K F' T) :
    H1 K F S →ₗ[K] H1 K F' T :=
  (coboundariesIn K F S).mapQ (coboundariesIn K F' T)
    (LinearMap.codRestrict (cocycles K F' T) ((pullbackPair φ).domRestrict (cocycles K F S))
      (fun c => hZ c c.2))
    (fun c hc => hB c hc)

theorem H1.map_mk (S : Set (Place K F)) (T : Set (Place K F')) (φ : F →ₐ[K] F')
    (hZ : ∀ c ∈ cocycles K F S, pullbackPair φ c ∈ cocycles K F' T)
    (hB : ∀ c ∈ coboundaries K F S, pullbackPair φ c ∈ coboundaries K F' T)
    (c : ↥(cocycles K F S)) :
    H1.map S T φ hZ hB (H1.mk S c) = H1.mk T ⟨pullbackPair φ c, hZ c c.2⟩ := rfl

end Map

section Frobenius

variable {K F}
variable (p : ℕ) [Fact p.Prime] [CharP K p]

omit [Fact p.Prime] in

theorem D_pow_char (g : F) : D K F (g ^ p) = 0 := by
  haveI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F p, zero_smul]

def frobPair : (Ω[F⁄K] × F) →ₛₗ[frobenius K p] (Ω[F⁄K] × F) where
  toFun c := (0, c.2 ^ p)
  map_add' c c' := by
    ext
    · simp
    · haveI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
      show (c.2 + c'.2) ^ p = c.2 ^ p + c'.2 ^ p
      exact add_pow_char (p := p) c.2 c'.2
  map_smul' a c := by
    ext
    · simp
    · simp only [Prod.smul_snd, frobenius_def, Algebra.smul_def, mul_pow, map_pow]

variable (S : Set (Place K F))

theorem frobPair_mem_cocycles (c : ↥(cocycles K F S)) : frobPair p (c : Ω[F⁄K] × F) ∈ cocycles K F S := by
  refine ⟨fun v _ => v.hasPoleOrderLE_zero_right 0, fun v _ => ?_⟩
  show v.HasPoleOrderLE 1 ((0 : Ω[F⁄K]) - D K F ((c : Ω[F⁄K] × F).2 ^ p))
  rw [D_pow_char, sub_zero]
  exact v.hasPoleOrderLE_zero_right 1

def frobCocycles : ↥(cocycles K F S) →ₛₗ[frobenius K p] ↥(cocycles K F S) :=
  LinearMap.codRestrict (cocycles K F S) ((frobPair p).domRestrict (cocycles K F S))
    (frobPair_mem_cocycles p S)

theorem coboundariesIn_le_comap_frobCocycles :
    coboundariesIn K F S ≤ (coboundariesIn K F S).comap (frobCocycles p S) := by
  intro c hc

  have hc' : (c : Ω[F⁄K] × F) ∈ exactPart K F S ⊔ localPart K F S := hc
  show frobPair p (c : Ω[F⁄K] × F) ∈ coboundaries K F S
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hc'
  rw [← hyz, map_add]
  refine add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · obtain ⟨h, hh, rfl⟩ := hy
    refine ⟨h ^ p, fun v hv => pow_mem (hh v hv) p, ?_⟩
    show ((0 : Ω[F⁄K]), h ^ p) = (D K F (h ^ p), h ^ p)
    rw [D_pow_char]
  · exact ⟨rfl, fun v hv => pow_mem (hz.2 v hv) p⟩

def H1.frob : H1 K F S →ₛₗ[frobenius K p] H1 K F S :=
  (coboundariesIn K F S).mapQ (coboundariesIn K F S) (frobCocycles p S)
    (coboundariesIn_le_comap_frobCocycles p S)

end Frobenius

section Cartier

variable {K F}
variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

structure CartierHypotheses (C : Ω[F⁄K] →+ Ω[F⁄K]) : Prop where
  semi : ∀ (a : K) (ω : Ω[F⁄K]), C (a • ω) = (frobeniusEquiv K p).symm a • C ω
  ker : ∀ f : F, C (D K F f) = 0
  regular : ∀ (v : Place K F) (ω : Ω[F⁄K]), v.HasPoleOrderLE 0 ω → v.HasPoleOrderLE 0 (C ω)
  log : ∀ (v : Place K F) (ω : Ω[F⁄K]), v.HasPoleOrderLE 1 ω → v.HasPoleOrderLE 1 (C ω)

variable {p}
variable {C : Ω[F⁄K] →+ Ω[F⁄K]} (hC : CartierHypotheses p C)
variable (S : Set (Place K F))

def cartierPair :
    (Ω[F⁄K] × F) →ₛₗ[((frobeniusEquiv K p).symm : K →+* K)] (Ω[F⁄K] × F) where
  toFun c := (C c.1, 0)
  map_add' c c' := by ext <;> simp [map_add]
  map_smul' a c := by
    ext
    · simp only [Prod.smul_fst, RingHom.coe_coe]; exact hC.semi a c.1
    · simp

theorem cartierPair_mem_cocycles (c : ↥(cocycles K F S)) :
    cartierPair hC (c : Ω[F⁄K] × F) ∈ cocycles K F S := by
  obtain ⟨hoff, hon⟩ := c.2
  refine ⟨fun v hv => hC.regular v _ (hoff v hv), fun v hv => ?_⟩
  show v.HasPoleOrderLE 1 (C (c : Ω[F⁄K] × F).1 - D K F 0)

  have h : C (c : Ω[F⁄K] × F).1 = C ((c : Ω[F⁄K] × F).1 - D K F (c : Ω[F⁄K] × F).2) := by
    rw [map_sub, hC.ker, sub_zero]
  rw [map_zero, sub_zero, h]
  exact hC.log v _ (hon v hv)

def cartierCocycles :
    ↥(cocycles K F S) →ₛₗ[((frobeniusEquiv K p).symm : K →+* K)] ↥(cocycles K F S) :=
  LinearMap.codRestrict (cocycles K F S) ((cartierPair hC).domRestrict (cocycles K F S))
    (cartierPair_mem_cocycles hC S)

theorem coboundariesIn_le_comap_cartierCocycles :
    coboundariesIn K F S ≤ (coboundariesIn K F S).comap (cartierCocycles hC S) := by
  intro c hc

  have hc' : (c : Ω[F⁄K] × F) ∈ exactPart K F S ⊔ localPart K F S := hc
  show cartierPair hC (c : Ω[F⁄K] × F) ∈ coboundaries K F S
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hc'
  obtain ⟨h, hh, rfl⟩ := hy
  have hy0 : cartierPair hC (D K F h, h) = 0 :=
    Prod.ext (by show C (D K F h) = 0; exact hC.ker h) rfl
  have hz0 : cartierPair hC z = 0 :=
    Prod.ext (by show C z.1 = 0; rw [hz.1, map_zero]) rfl
  rw [← hyz, map_add, hy0, hz0, add_zero]
  exact zero_mem _

def H1.cartier :
    H1 K F S →ₛₗ[((frobeniusEquiv K p).symm : K →+* K)] H1 K F S :=
  (coboundariesIn K F S).mapQ (coboundariesIn K F S) (cartierCocycles hC S)
    (coboundariesIn_le_comap_cartierCocycles hC S)

end Cartier

end LogDeRham

end AlgebraicCurve

end



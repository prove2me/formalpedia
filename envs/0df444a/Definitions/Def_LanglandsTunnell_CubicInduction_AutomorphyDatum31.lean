-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
-- name    : LanglandsTunnell_CubicInduction_AutomorphyDatum31
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/e7865e61-4700-568d-9c9e-229bab23b93f
-- title:
--   Local-to-adelic embeddings, congruence sets, GL₃ automorphy datum
-- statement:
--   For a Dedekind domain $R$ with fraction field $K$, a finite index type $\iota$ and a finite place $v$ of $R$, `localMatN` sends a matrix over the completion $K_v$ to the matrix over the finite adeles whose $v$-component is the given matrix and whose component at every $w \neq v$ is the identity matrix; `localMatN_apply_self`, `localMatN_apply_of_ne`, `localMatN_one`, `localMatN_mul` and the two extensionality lemmas `matrixFin_ext`, `matrixAdele_ext` (equality of adelic matrices is tested place by place, resp. on the archimedean and finite parts) give the multiplicativity used to upgrade it to a monoid homomorphism `localEmbedN` on general linear groups. Likewise `finMatN` puts the identity in the archimedean slot, giving `finEmbedN`, and `localToAdelicN` is their composite $\mathrm{GL}_\iota(K_v) \to \mathrm{GL}_\iota(\mathbb{A}_K)$; `localToAdelic3` is the case $\iota = \mathrm{Fin}\,3$, $R = \mathcal{O}_{\mathbb{Q}}$, $K = \mathbb{Q}$.
--
--   For a finite place $v$ of $\mathbb{Q}$ and $a \in \mathbb{N}$, `converseCongruenceSet3 v a` is the set of $k$ in the local maximal compact subgroup of $\mathrm{GL}_3(\mathbb{Q}_v)$ whose entries in positions $(1,2)$ and $(3,1)$ have valuation at most $\exp(-a)$ and whose $(3,2)$ entry has valuation at most $\exp(-2a)$, i.e. lie in $\mathfrak{p}_v^{a}$, $\mathfrak{p}_v^{a}$, $\mathfrak{p}_v^{2a}$; the identity belongs to it. `parabolicCongruenceSet3 v a` consists of products $p\,k$ with the $(3,1)$ and $(3,2)$ entries of $p$ zero and $k$ in the congruence set. `IsCongruenceEquivariantAt`/`IsCongruenceEquivariantAlong` assert $W(gk) = \chi(u)\,W(g)$ for all $g$ and all $k$ in the congruence set, where $u$ is a unit equal to the $(3,3)$ entry of $k$ (in the adelic version $k$ is pushed forward by `localToAdelic3`). `HasVanishingUnipotentIntegralAt`/`HasVanishingUnipotentIntegralAlong` assert that for every $g$ the integral, against the self-dual Haar measure of $\mathbb{Q}_v$ over $\{x : \mathrm{v}(x) \le \exp(1)\} = \mathfrak{p}_v^{-1}$, of $W(g \cdot n(x))$ vanishes, $n(x)$ being the unipotent with $x$ in position $(2,3)$.
--
--   `AutomorphyDatum31 pins ψ S a ω W lam1 lam2` is a structure carrying a function `form` on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ together with, as fields: continuity; left invariance under $\mathrm{GL}_3(\mathbb{Q})$; the central character law with $\omega$; moderate growth; congruence equivariance at each $v \in S$ of level $a(v)$ through the local component of $\omega$; the identity $\mathrm{whittaker3}\,\psi\,(\mathrm{form})(g) = W(g)$ at every $g$ whose components at the places of $S$ lie in the congruence sets; vanishing of the double integral of `form` over the unipotent radical $\mathrm{radicalP21}$ (against the measure carried by `pins`) at every $g$ whose components at the places of $S$ lie in the parabolic sets; and, at each $p \notin S$, right invariance under the image of the local maximal compact and the coset-eigenfunction property for the two Hecke generators with eigenvalues $\mathrm{lam1}(p)$, $\mathrm{lam2}(p)$. `AutomorphyDatum31.zero` exhibits such a datum with $W = 0$, given by the zero function.
--
--   **Relation to Mathlib.** Mathlib supplies the finite adele and adele rings, adic completions, general linear groups and Haar measure; the congruence sets, the equivariance and unipotent-integral predicates and the automorphy datum are the project's own. The matrix constructions repeat, for an arbitrary finite index type, the $\mathrm{GL}_2$ embeddings [`AdelicDock.localMat`](../def/AdelicDock_LocalEmbedding.html#L57)/[`AdelicDock.finMat`](../def/AdelicDock_LocalEmbedding.html#L122).
--
--   **Where it is used.** These are the hypotheses of a converse theorem for $\mathrm{GL}_3$ in the form needed for Langlands–Tunnell: the datum records exactly the automorphy, growth, Hecke and local congruence properties of a candidate form on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ attached to a cubic induction. Langlands–Tunnell in turn provides the modularity of the mod-$3$ representation with which the Wiles argument for Fermat's Last Theorem begins.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Embeddings

variable (ι : Type*) [Fintype ι] [DecidableEq ι]
variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem matrixFin_ext {M N : Matrix ι ι (FiniteAdeleRing R K)}
    (h : ∀ w : HeightOneSpectrum R,
      (AdelicLevel.finAdeleEval R K w).mapMatrix M = (AdelicLevel.finAdeleEval R K w).mapMatrix N) :
    M = N := by
  ext i j w : 2
  have hw := congrFun (congrFun (h w) i) j
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply] using hw

theorem matrixAdele_ext {M N : Matrix ι ι (AdeleRing R K)}
    (h₁ : (AdelicLevel.adeleArch R K).mapMatrix M = (AdelicLevel.adeleArch R K).mapMatrix N)
    (h₂ : (AdelicLevel.adeleFin R K).mapMatrix M = (AdelicLevel.adeleFin R K).mapMatrix N) :
    M = N := by
  ext i j
  have hw₁ := congrFun (congrFun h₁ i) j
  have hw₂ := congrFun (congrFun h₂ i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply,
    AdelicLevel.adeleFin_apply] at hw₁ hw₂
  exact Prod.ext hw₁ hw₂

variable (v : HeightOneSpectrum R)

def localMatN (g : Matrix ι ι (v.adicCompletion K)) : Matrix ι ι (FiniteAdeleRing R K) :=
  Matrix.of fun i j => AdelicDock.splice R K v ((1 : Matrix ι ι (FiniteAdeleRing R K)) i j) (g i j)

omit [Fintype ι] in
theorem localMatN_apply_self (g : Matrix ι ι (v.adicCompletion K)) (i j : ι) :
    localMatN ι R K v g i j v = g i j := by
  simp [localMatN]

omit [Fintype ι] in
theorem localMatN_apply_of_ne (g : Matrix ι ι (v.adicCompletion K)) (i j : ι)
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    localMatN ι R K v g i j w = (1 : Matrix ι ι (w.adicCompletion K)) i j := by
  simp only [localMatN, Matrix.of_apply, AdelicDock.splice_apply_of_ne R K v _ _ hw]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem mapMatrix_localMatN_self (g : Matrix ι ι (v.adicCompletion K)) :
    (AdelicLevel.finAdeleEval R K v).mapMatrix (localMatN ι R K v g) = g := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply,
    localMatN_apply_self]

theorem mapMatrix_localMatN_of_ne (g : Matrix ι ι (v.adicCompletion K))
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    (AdelicLevel.finAdeleEval R K w).mapMatrix (localMatN ι R K v g) = 1 := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply,
    localMatN_apply_of_ne ι R K v g i j hw]

theorem localMatN_one : localMatN ι R K v 1 = 1 := by
  refine matrixFin_ext ι R K fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [mapMatrix_localMatN_self, map_one]
  · rw [mapMatrix_localMatN_of_ne ι R K v _ hw, map_one]

theorem localMatN_mul (g h : Matrix ι ι (v.adicCompletion K)) :
    localMatN ι R K v (g * h) = localMatN ι R K v g * localMatN ι R K v h := by
  refine matrixFin_ext ι R K fun w => ?_
  by_cases hw : w = v
  · subst hw
    rw [map_mul, mapMatrix_localMatN_self, mapMatrix_localMatN_self, mapMatrix_localMatN_self]
  · rw [map_mul, mapMatrix_localMatN_of_ne ι R K v _ hw, mapMatrix_localMatN_of_ne ι R K v _ hw,
      mapMatrix_localMatN_of_ne ι R K v _ hw, mul_one]

def localEmbedN : GL ι (v.adicCompletion K) →* GL ι (FiniteAdeleRing R K) where
  toFun g :=
    { val := localMatN ι R K v g
      inv := localMatN ι R K v ((g⁻¹ : GL ι (v.adicCompletion K)) : Matrix _ _ _)
      val_inv := by rw [← localMatN_mul, Units.mul_inv, localMatN_one]
      inv_val := by rw [← localMatN_mul, Units.inv_mul, localMatN_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact localMatN_one ι R K v)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact localMatN_mul ι R K v _ _)

def finMatN (g : Matrix ι ι (FiniteAdeleRing R K)) : Matrix ι ι (AdeleRing R K) :=
  Matrix.of fun i j => (((1 : Matrix ι ι (InfiniteAdeleRing K)) i j, g i j) : AdeleRing R K)

theorem mapMatrix_arch_finMatN (g : Matrix ι ι (FiniteAdeleRing R K)) :
    (AdelicLevel.adeleArch R K).mapMatrix (finMatN ι R K g) = 1 := by
  ext i j
  simp [finMatN, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply]

theorem mapMatrix_fin_finMatN (g : Matrix ι ι (FiniteAdeleRing R K)) :
    (AdelicLevel.adeleFin R K).mapMatrix (finMatN ι R K g) = g := by
  ext i j
  simp [finMatN, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply]

theorem finMatN_one : finMatN ι R K 1 = 1 :=
  matrixAdele_ext ι R K (by rw [mapMatrix_arch_finMatN, map_one])
    (by rw [mapMatrix_fin_finMatN, map_one])

theorem finMatN_mul (g h : Matrix ι ι (FiniteAdeleRing R K)) :
    finMatN ι R K (g * h) = finMatN ι R K g * finMatN ι R K h :=
  matrixAdele_ext ι R K
    (by rw [map_mul, mapMatrix_arch_finMatN, mapMatrix_arch_finMatN, mapMatrix_arch_finMatN, mul_one])
    (by rw [map_mul, mapMatrix_fin_finMatN, mapMatrix_fin_finMatN, mapMatrix_fin_finMatN])

def finEmbedN : GL ι (FiniteAdeleRing R K) →* GL ι (AdeleRing R K) where
  toFun g :=
    { val := finMatN ι R K g
      inv := finMatN ι R K ((g⁻¹ : GL ι (FiniteAdeleRing R K)) : Matrix _ _ _)
      val_inv := by rw [← finMatN_mul, Units.mul_inv, finMatN_one]
      inv_val := by rw [← finMatN_mul, Units.inv_mul, finMatN_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact finMatN_one ι R K)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact finMatN_mul ι R K _ _)

def localToAdelicN : GL ι (v.adicCompletion K) →* GL ι (AdeleRing R K) :=
  (finEmbedN ι R K).comp (localEmbedN ι R K v)

end Embeddings

section LocalThree

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev localToAdelic3 : LocalGL3 v →* AdelicGL 3 (𝓞 ℚ) ℚ :=
  localToAdelicN (Fin 3) (𝓞 ℚ) ℚ v

def converseCongruenceSet3 (a : ℕ) : Set (LocalGL3 v) :=
  {k | k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1) ≤ WithZero.exp (-(a : ℤ)) ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0) ≤ WithZero.exp (-(a : ℤ)) ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1) ≤ WithZero.exp (-(2 * (a : ℤ)))}

theorem one_mem_converseCongruenceSet3 (a : ℕ) : (1 : LocalGL3 v) ∈ converseCongruenceSet3 v a := by
  refine ⟨Subgroup.one_mem _, ?_, ?_, ?_⟩
  · rw [Units.val_one, Matrix.one_apply_ne (by decide), map_zero]
    exact zero_le
  · rw [Units.val_one, Matrix.one_apply_ne (by decide), map_zero]
    exact zero_le
  · rw [Units.val_one, Matrix.one_apply_ne (by decide), map_zero]
    exact zero_le

def parabolicCongruenceSet3 (a : ℕ) : Set (LocalGL3 v) :=
  {g | ∃ p k : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 ∧
    (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 ∧ k ∈ converseCongruenceSet3 v a ∧
    g = p * k}

def IsCongruenceEquivariantAt (a : ℕ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (W : LocalGL3 v → ℂ) : Prop :=
  ∀ k ∈ converseCongruenceSet3 v a, ∀ u : (v.adicCompletion ℚ)ˣ,
    (u : v.adicCompletion ℚ) = (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 →
      ∀ g, W (g * k) = ((χ u : ℂˣ) : ℂ) * W g

def HasVanishingUnipotentIntegralAt (W : LocalGL3 v → ℂ) : Prop :=
  letI := LanglandsTunnell.TateLocal.localBorel ℚ v
  ∀ g : LocalGL3 v,
    (∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (1 : ℤ)}, W (g * upperUnipotent3 0 x 0)
      ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)) = 0

def HasVanishingUnipotentIntegralAlong (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  letI := LanglandsTunnell.TateLocal.localBorel ℚ v
  ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
    (∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (1 : ℤ)},
        W (g * localToAdelic3 v (upperUnipotent3 0 x 0))
      ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)) = 0

def IsCongruenceEquivariantAlong (a : ℕ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∀ k ∈ converseCongruenceSet3 v a, ∀ u : (v.adicCompletion ℚ)ˣ,
    (u : v.adicCompletion ℚ) = (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 →
      ∀ g, W (g * localToAdelic3 v k) = ((χ u : ℂˣ) : ℂ) * W g

end LocalThree

section Global

structure AutomorphyDatum31 (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (a : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ) where

  form : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ

  continuous : Continuous form
  automorphic : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
    form (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = form g
  central : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
    form (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * form g
  moderateGrowth : IsModerateGrowth3 ℚ form
  equivariant : ∀ v ∈ S, IsCongruenceEquivariantAlong v (a v) (TateGlobal.localChar ω v) form
  whittaker_eq : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
    (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v (a v)) →
      whittaker3 pins ψ form g = W g
  cuspidalP21 : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
    (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g ∈ parabolicCongruenceSet3 v (a v)) →
      (letI := pins.nS; ∫ x, ∫ y, form (radicalP21 ![x, y] * g) ∂pins.ν ∂pins.ν) = 0
  heckeInvariant : ∀ p, p ∉ S →
    IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) form
  hecke1 : ∀ p, p ∉ S →
    IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) form (lam1 p)
  hecke2 : ∀ p, p ∉ S →
    IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) form (lam2 p)

def AutomorphyDatum31.zero (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (a : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ) :
    AutomorphyDatum31 pins ψ S a ω 0 lam1 lam2 where
  form := 0
  continuous := continuous_const
  automorphic := fun _ _ => rfl
  central := fun _ _ => by simp
  moderateGrowth := isModerateGrowth3_zero ℚ
  equivariant := fun _ _ _ _ _ _ _ => by simp
  whittaker_eq := fun _ _ => by simp only [whittaker3, Pi.zero_apply, zero_mul, MeasureTheory.integral_zero]
  cuspidalP21 := fun _ _ => by simp
  heckeInvariant := fun _ _ _ _ _ => rfl
  hecke1 := fun p _ => isCosetEigenfunction_zero _ _ (lam1 p)
  hecke2 := fun p _ => isCosetEigenfunction_zero _ _ (lam2 p)

end Global

end LanglandsTunnell.CubicInduction

end

#check @LanglandsTunnell.CubicInduction.localToAdelic3
#check @LanglandsTunnell.CubicInduction.converseCongruenceSet3
#check @LanglandsTunnell.CubicInduction.IsCongruenceEquivariantAt
#check @LanglandsTunnell.CubicInduction.HasVanishingUnipotentIntegralAt
#check @LanglandsTunnell.CubicInduction.AutomorphyDatum31
#check @LanglandsTunnell.CubicInduction.HasVanishingUnipotentIntegralAlong
#check @LanglandsTunnell.CubicInduction.IsCongruenceEquivariantAlong
#print axioms LanglandsTunnell.CubicInduction.localToAdelicN
#print axioms LanglandsTunnell.CubicInduction.one_mem_converseCongruenceSet3
#print axioms LanglandsTunnell.CubicInduction.AutomorphyDatum31.zero



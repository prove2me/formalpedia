-- Prove2me | Definitions.Def_ChapterSmComparison
-- name    : ChapterSmComparison
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-04T15:03:10.119555+00:00
-- url     : https://prove2.me/theorems/678ceacb-39a0-4945-86a5-c4105bc74b1c
-- title:
--   The Lean 4 theorem `card_smConf` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSmComparison.lean`): generated def bundle for ChapterSmComparison. See BookProof/ChapterSmComparison.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSmComparison.lean

import Definitions.Def_ChapterBddBelowWallEsa
import Definitions.Def_ChapterSmHamiltonian
import Definitions.Def_ChapterWallEsaBddBelow
import Definitions.Def_ChapterTensorSumChain
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterTensorSumEsa
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Mathlib
import Theorems.Thm_BookProof_ScalaronEsa_ccDomain_dense
import Theorems.Thm_BookProof_ScalaronWallEsa_wallHam_symmetricOn
import Theorems.Thm_BookProof_SmHamiltonian_smPi_symmetricOn
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
import Theorems.Thm_BookProof_YangMillsHermite_mulOp_polySym
import Theorems.Thm_BookProof_YangMillsHermite_realCoeff_X
import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_symmetricOn_op
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_mul
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_add
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_sum
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_smul


/-!
# The Standard Model comparison operator `N`

Step 2 of the Standard-Model work order of `CONSOLIDATED_PLAN.md` (§D6b-SM.2 / D6b-SM.4):
the Faris–Lavine comparison operator of the Standard Model,

```
N = N₀ + c₀,  c₀ ≥ 1,
N₀ = Σ_{G,W}  ( π² + q⁴ + Σ_j (∂_j q)² )
   + Σ_B      ( π² + q²  + Σ_j (∂_j q)² )
   + Σ_φ      ( π² + q⁴ + Σ_j (∂_j q)² ),
```

written on the same Gauss–polynomial core of `L²(ℝ¹⁶³)` that carries the Hamiltonian of
`BookProof.ChapterSmHamiltonian`.  The structural point of §D6b-SM.2 is the *mix*: the
confinement is **quartic** in the non-abelian and Higgs coordinates and **quadratic** in the
abelian field and in the derivative coordinates.  `smComparison` is exactly that operator:
every one of its summands is a square of a symmetric operator (`π`, `q²`, `q`), plus the
shift `c₀`.

## What is proved

* `card_smConf = 160` — the recount of the confining squares: `37` quartic
  (`24` gluon + `9` weak + `4` Higgs), `3` abelian quadratic, `120` derivative quadratic;
* `smComparison` — the operator, `smComparison_symmetricOn` — it is symmetric on the core;
* `smComparison_quadForm` — its quadratic form is the sum of squares plus `c₀‖x‖²`;
* **`sm_N_positive`** — `⟪x, N x⟫ ≥ ‖x‖²` for `c₀ ≥ 1`: the positivity and the lower bound
  `N ≥ 1` of CHECK 9c, which is what makes `N + 1` a candidate comparison operator;
* `quarticEsaOp`, `quadraticEsaOp`, `smDynChain`, **`sm_N_dyn_esa`** — the confining
  one-dimensional factors `−d²/dq² + q⁴` and `−d²/dq² + q²` are essentially self-adjoint on
  the compactly supported smooth core (`BookProof.WallEsaBddBelow`), and their `40`-fold
  tensor sum — the *dynamical* part of `N₀`, one factor for each momentum-carrying
  coordinate — is essentially self-adjoint on the algebraic tensor product of the `40`
  cores, by `BookProof.TensorSumChain.chain_esa`.  `sm_N_dyn_stone_flow` is the unitary
  group it generates.
* **Accounting identity (why `N` carries no separate BRST gauge-fixing term).**  On the
  temporal-gauge slice `A₀ = 0` the book's BRST-exact contribution `{Ω, Ψ}` with
  `Ψ = i ψ_a A_{0a}` vanishes (`BookProof.BookBrstGaugeFixing.bookGfTerm_eq_zero_of_Afield0`,
  SM instance `sm_bookGfTerm_eq_zero_of_Afield0` in `ChapterBookBrstInstances.lean`;
  Cadabra PART F CHECK 29/30a–c in `../unfer/docs/faris_lavine_n_sm.cdb`).  Hence the
  comparison operator of record is exactly `N = N₀ + c₀ I` with no extra gauge-fixing/ghost
  summand, in parallel with `smHamiltonian` in `ChapterSmHamiltonian.lean`.

## Honest boundary

Two things are **not** claimed here, and the plan's Faris–Lavine chain for the Standard
Model is not closed by this module:

1. `sm_N_dyn_esa` is the essential self-adjointness of the *uncoupled confining chain* — the
   `40` dynamical `(π² + q⁴)` / `(π² + q²)` factors — realized on the tensor product of the
   `40` one-dimensional spaces.  The derivative-coordinate summands `Σ_j (∂_j q)²` of `N₀`,
   which are multiplication operators without a conjugate momentum, are not part of that
   chain, and no statement is made about `N` on the Gauss–polynomial core beyond symmetry
   and the lower bound.
2. The three Faris–Lavine hypotheses of §D6b-SM.3 — the relative bound `±h ≤ c₁N`, the
   first-commutator bound and the double-commutator bound — are certified symbolically in
   the Cadabra module (CHECK 1–28) and are **not** formalized here.  They are not needed for
   what `BookProof.ChapterSmOuterFock` proves: the Standard-Model one-particle operator of
   this development is a positive sum of squares, so the doctrine's default instrument for
   it is Friedrichs, not Faris–Lavine.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmComparison

open MvPolynomial
open BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.ScalaronWallEsa BookProof.ScalaronEsa BookProof.WallEsaBddBelow
open BookProof.BddBelowWallEsa
open BookProof.TensorSumChain BookProof.TensorCore BookProof.TensorSumEsa
open BookProof.EsaClosure BookProof.GraphCore
open BookProof.StoneBridge BookProof.ChapterStoneResolvent
open MeasureTheory

noncomputable section

/-! ## 1. The confining squares -/

/-- The labels of the confining squares of `N₀`: the `37` coordinates with quartic
confinement (gluon, weak, Higgs), the `3` abelian coordinates with quadratic confinement,
and the `120` derivative coordinates with quadratic confinement. -/
abbrev SmConf : Type :=
  ((Fin 8 × Fin 3) ⊕ (Fin 3 × Fin 3) ⊕ Fin 4)
    ⊕ Fin 3
    ⊕ ((Fin 8 × Fin 3 × Fin 3) ⊕ (Fin 3 × Fin 3 × Fin 3) ⊕ (Fin 3 × Fin 3) ⊕ (Fin 4 × Fin 3))

/-- **The recount of the confining squares**: `37 + 3 + 120 = 160`. -/
theorem card_smConf : Fintype.card SmConf = 160 := by simp

/-- The labelling of the `160` confining squares. -/
def smConfFin : SmConf ≃ Fin 160 := Fintype.equivFinOfCardEq card_smConf

/-- The polynomial squared by a confinement label: `q²` for the quartically confined
coordinates (so that its square is `q⁴`) and `q` for the quadratically confined ones. -/
def smConfPoly : SmConf → MvPolynomial (Fin 163) ℂ
  | Sum.inl (Sum.inl (a, i)) => X (smG a i) * X (smG a i)
  | Sum.inl (Sum.inr (Sum.inl (k, i))) => X (smW k i) * X (smW k i)
  | Sum.inl (Sum.inr (Sum.inr a)) => X (smPhi a) * X (smPhi a)
  | Sum.inr (Sum.inl i) => X (smB i)
  | Sum.inr (Sum.inr (Sum.inl (a, i, j))) => X (smDG a i j)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (k, i, j)))) => X (smDW k i j)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j))))) => X (smDB i j)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (a, j))))) => X (smDPhi a j)

theorem realCoeff_smConfPoly (s : SmConf) : RealCoeff (smConfPoly s) := by
  rcases s with (⟨a, i⟩ | ⟨k, i⟩ | a) | i | (⟨a, i, j⟩ | ⟨k, i, j⟩ | ⟨i, j⟩ | ⟨a, j⟩)
  · exact (realCoeff_X _).mul (realCoeff_X _)
  · exact (realCoeff_X _).mul (realCoeff_X _)
  · exact (realCoeff_X _).mul (realCoeff_X _)
  · exact realCoeff_X _
  · exact realCoeff_X _
  · exact realCoeff_X _
  · exact realCoeff_X _
  · exact realCoeff_X _

/-- The confining multiplication operators on the Gauss–polynomial core. -/
def smConfField (s : Fin 160) :
    (polyGaussCore (d := 163)) →ₗ[ℂ] (polyGaussCore (d := 163)) :=
  (coreRepPoly 163).op (mulOp (smConfPoly (smConfFin.symm s)))

theorem smConfField_symmetricOn (s : Fin 160) :
    SymmetricOn (polyGaussCore (d := 163))
      ((polyGaussCore (d := 163)).subtype.comp (smConfField s)) :=
  (coreRepPoly 163).symmetricOn_op (mulOp_polySym (realCoeff_smConfPoly _))

/-! ## 2. The comparison operator -/

/-- **The Standard-Model comparison operator** `N = N₀ + c₀` of §D6b-SM.2 on the
Gauss–polynomial core of `L²(ℝ¹⁶³)`: the `40` momentum squares, the `160` confining squares
— quartic for the non-abelian and Higgs coordinates, quadratic for the abelian field and
for the derivative coordinates — and the shift `c₀`. -/
def smComparison (c0 : ℝ) : (polyGaussCore (d := 163)) →ₗ[ℂ] L2d 163 :=
  (2 : ℂ) • weylOp smPi smConfField + ((c0 : ℝ) : ℂ) • (polyGaussCore (d := 163)).subtype

theorem smComparison_symmetricOn (c0 : ℝ) :
    SymmetricOn (polyGaussCore (d := 163)) (smComparison c0) := by
  intro x y
  have hw := weylOpDom_symmetricOn smPi_symmetricOn smConfField_symmetricOn x y
  simp only [smComparison, LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    map_ofNat]
  rw [hw]

/-- The quadratic form of the comparison operator: the sum of the squares plus `c₀‖x‖²`. -/
theorem smComparison_quadForm (c0 : ℝ) (x : polyGaussCore (d := 163)) :
    quadForm (smComparison c0) x
      = 2 * quadForm (weylOp smPi smConfField) x + c0 * ‖((x : polyGaussCore (d := 163)) :
          L2d 163)‖ ^ 2 := by
  have h1 : (inner ℂ ((x : polyGaussCore (d := 163)) : L2d 163) (smComparison c0 x) : ℂ)
      = (2 : ℂ) * inner ℂ ((x : polyGaussCore (d := 163)) : L2d 163)
          (weylOp smPi smConfField x)
        + ((c0 : ℝ) : ℂ) * inner ℂ ((x : polyGaussCore (d := 163)) : L2d 163)
          ((x : polyGaussCore (d := 163)) : L2d 163) := by
    simp [smComparison, LinearMap.add_apply, LinearMap.smul_apply, smul_apply, map_smul,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      inner_self_eq_norm_sq_to_K, real_inner_self_eq_norm_sq, map_ofNat]
    show inner ℂ ((x : polyGaussCore (d := 163)) : L2d 163)
        (((c0 : ℝ) : ℂ) • ((x : polyGaussCore (d := 163)) : L2d 163))
      = ((c0 : ℝ) : ℂ) * (‖((x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 : ℂ)
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
    rfl
  have h2 : (inner ℂ ((x : polyGaussCore (d := 163)) : L2d 163)
      ((x : polyGaussCore (d := 163)) : L2d 163) : ℂ)
      = ((‖((x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [quadForm, h1, h2, quadForm]
  simp only [Complex.ofReal_pow, Complex.add_re, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, sub_zero, Complex.ofReal_re, Complex.ofReal_im, add_right_inj,
    mul_eq_mul_left_iff]
  left
  norm_cast

/-- **`N ≥ 1` (CHECK 9c).**  Every summand of `N₀` is a square of a symmetric operator, so
the quadratic form of `N` is at least `c₀‖x‖²`; for `c₀ ≥ 1` the comparison operator is
bounded below by the identity, which is the positivity the Faris–Lavine criterion asks
of it. -/
theorem sm_N_positive {c0 : ℝ} (hc0 : 1 ≤ c0) (x : polyGaussCore (d := 163)) :
    ‖((x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 ≤ quadForm (smComparison c0) x := by
  have hnn : 0 ≤ quadForm (weylOp smPi smConfField) x :=
    weylOpDom_quadForm_nonneg smPi_symmetricOn smConfField_symmetricOn x
  have hx : (0 : ℝ) ≤ ‖((x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 := by positivity
  rw [smComparison_quadForm]
  nlinarith

/-- In particular the comparison operator is positive. -/
theorem sm_N_quadForm_nonneg {c0 : ℝ} (hc0 : 1 ≤ c0) (x : polyGaussCore (d := 163)) :
    0 ≤ quadForm (smComparison c0) x :=
  le_trans (by positivity) (sm_N_positive hc0 x)

/-! ## 3. The confining one-dimensional factors, and their tensor sum -/

theorem contDiff_pow4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : ℝ => x ^ 4 :=
  contDiff_id.pow 4

theorem contDiff_pow2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : ℝ => x ^ 2 :=
  contDiff_id.pow 2

/-- **The quartic confining factor** `−d²/dq² + q⁴`, essentially self-adjoint on the
compactly supported smooth core of `L²(ℝ)`: the one-dimensional summand of `N₀` attached to
a gluon, weak or Higgs coordinate. -/
def quarticEsaOp : EsaOp where
  space := ⟨Lp ℂ 2 (volume : Measure ℝ)⟩
  complete := inferInstanceAs (CompleteSpace (Lp ℂ 2 (volume : Measure ℝ)))
  dom := ccDomain ℝ
  op := wallHam (fun x : ℝ => x ^ 4) contDiff_pow4
  dense := ccDomain_dense
  sym := wallHam_symmetricOn _ _
  esa := wallHam_essentiallySelfAdjoint_of_bddBelow _ _ (K := 0) fun x => by
    have h : (0 : ℝ) ≤ x ^ 4 := by positivity
    linarith

/-- **The quadratic confining factor** `−d²/dq² + q²`, the one-dimensional summand of `N₀`
attached to the abelian hypercharge coordinate. -/
def quadraticEsaOp : EsaOp where
  space := ⟨Lp ℂ 2 (volume : Measure ℝ)⟩
  complete := inferInstanceAs (CompleteSpace (Lp ℂ 2 (volume : Measure ℝ)))
  dom := ccDomain ℝ
  op := wallHam (fun x : ℝ => x ^ 2) contDiff_pow2
  dense := ccDomain_dense
  sym := wallHam_symmetricOn _ _
  esa := wallHam_essentiallySelfAdjoint_of_bddBelow _ _ (K := 0) fun x => by
    have h : (0 : ℝ) ≤ x ^ 2 := by positivity
    linarith

/-- **The dynamical part of `N₀` as a tensor sum**: one confining factor for each of the
`40` momentum-carrying coordinates — `37` quartic (gluon, weak, Higgs) and `3` quadratic
(hypercharge). -/
def smDynChain : EsaOp :=
  chain quarticEsaOp (List.replicate 36 quarticEsaOp ++ List.replicate 3 quadraticEsaOp)

/-! ## The two facts `chain` promises but does not declare

`Def_ChapterTensorSumChain` documents `chain_esa` and `chain_stone_flow` and declares
neither: its 143 lines contain `EsaOp`, `pair`, `chain` and the two recursion equations, and
nothing else (no upstream `BookProof/ChapterTensorSumChain.lean` exists, so no revision ever
had them).  Both are one projection of `EsaOp`'s own fields — `esa` is the essential
self-adjointness and `exists_stone_flow_of_esa` turns that plus density and symmetry into the
Stone flow — so they are stated here rather than left as a citation of nothing. -/

/-- **The `n`-factor tensor sum is essentially self-adjoint** on the algebraic tensor product
of the domains: `chain E L` carries that proof as its `esa` field. -/
theorem chain_esa (E : EsaOp) (L : List EsaOp) :
    EssentiallySelfAdjointOn (chain E L).dom (chain E L).op :=
  (chain E L).esa

/-- **Its complete unitary flow**: the Stone group of the self-adjoint extension the same
data determines. -/
theorem chain_stone_flow (E : EsaOp) (L : List EsaOp) :
    ∃ (G : UnboundedSelfAdjoint (chain E L).space.carrier)
      (U : ℝ → ((chain E L).space.carrier →L[ℂ] (chain E L).space.carrier)),
      IsSelfAdjointExtension (chain E L).op G.op ∧ IsStoneFlow G U := by
  haveI := (chain E L).complete
  exact BookProof.StoneBridge.exists_stone_flow_of_esa (chain E L).op
    (chain E L).dense (chain E L).sym (chain E L).esa

/-- **The dynamical part of the Standard-Model comparison operator is essentially
self-adjoint.**  The `40` uncoupled confining degrees of freedom of `N₀` — `π² + q⁴` on the
non-abelian and Higgs coordinates, `π² + q²` on the abelian one — form a tensor sum, and a
tensor sum of essentially self-adjoint operators is essentially self-adjoint on the
algebraic tensor product of the domains. -/
theorem sm_N_dyn_esa :
    EssentiallySelfAdjointOn smDynChain.dom smDynChain.op :=
  chain_esa quarticEsaOp _

/-- The unitary group generated by the dynamical part of the comparison operator. -/
theorem sm_N_dyn_stone_flow :
    ∃ (G : UnboundedSelfAdjoint smDynChain.space.carrier)
      (U : ℝ → (smDynChain.space.carrier →L[ℂ] smDynChain.space.carrier)),
      IsSelfAdjointExtension smDynChain.op G.op ∧ IsStoneFlow G U :=
  chain_stone_flow quarticEsaOp _

end

end BookProof.SmComparison



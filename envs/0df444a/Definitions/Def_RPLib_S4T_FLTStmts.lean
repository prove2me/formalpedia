-- Prove2me | Definitions.Def_RPLib_S4T_FLTStmts
-- name    : RPLib_S4T_FLTStmts
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-16T07:13:43.549514+00:00
-- url     : https://prove2.me/theorems/c19bcd41-b9fb-439f-be1f-fdf0f1daf048
-- title:
--   Tate's isogeny theorem over finite fields (prime-to-$p$ form), library: the Proved FLT-project theorems used by the Tate route, as hypotheses
-- statement:
--   The Proved FLT-project theorems used by the Tate route, as hypotheses.
--
--   Each `S_<id8>` is the statement of the prove.me theorem with that uuid prefix (all Proved, env 0df444a, by the
--   FLT project), binders and conclusion copied byte-exact from the platform `formal_statement` (frontier cache, checked
--   equal to GET /theorems/<id>/graph). Locally these theorems are sorry stubs, so the library NEVER uses them as
--   lemmas: S4T files take `h : S_<id8>` as explicit hypotheses, and the platform reduction passes `@<theorem>`.
--
--   **Formalization note.** Library module of a formalization of Tate's isogeny theorem over finite fields in prime-to-$p$ form (ordinary elliptic curves with the same number of points are linked by $F$-isogenies $u, w$ with $w \circ u = [N]$, $p \nmid N$, stated through $F$-algebra maps of function fields), via Deuring lifting to characteristic $0$. It is conditional only on fifteen Proved prove2.me theorems of the FLT project, which enter as explicit hypotheses whose types are their exact statements (never as lemmas). Part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144, Theorem 1; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560, Chapter 4; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Sections III.6-III.7

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_DualIsogenyAPI

/-!
# S4T: the Proved FLT-project theorems used by the Tate route, as hypotheses

Each `S_<id8>` is the statement of the prove.me theorem with that uuid prefix (all Proved, env 0df444a, by the
FLT project), binders and conclusion copied byte-exact from the platform `formal_statement` (frontier cache, checked
equal to GET /theorems/<id>/graph). Locally these theorems are sorry stubs, so the library NEVER uses them as
lemmas: S4T files take `h : S_<id8>` as explicit hypotheses, and the platform reduction passes `@<theorem>`.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedVariables false

namespace RPLib.S4T.FLT

section


/-- `WeierstrassCurve.exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_mem_rationalHomSet` (0cf211ae-6c1d-5272-bfee-d6eb30d9d214). -/
def S_0cf211ae : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) [DecidableEq (AlgebraicClosure ℚ)] [DecidableEq (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p] (W : WeierstrassCurve (IsLocalRing.ResidueField A)) [W.IsElliptic] {α₀ : W.toAffine.Point →+ W.toAffine.Point} (hα₀ : α₀ ∈ WeierstrassCurve.rationalHomSet (IsLocalRing.ResidueField A) W W),
    ∃ (E : WeierstrassCurve A) (hΔ : (E.map (IsLocalRing.residue A)).Δ ≠ 0) (v : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField A)) (hv : v • E.map (IsLocalRing.residue A) = W), ∃ α ∈ WeierstrassCurve.rationalHomSet (AlgebraicClosure ℚ) (E.map A.subtype) (E.map A.subtype), ∀ P : (E.map A.subtype).toAffine.Point, (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv).symm (WeierstrassCurve.reduceHom hΔ (α P)) = α₀ ((WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv).symm (WeierstrassCurve.reduceHom hΔ P))

end

section


/-- `WeierstrassCurve.exists_ne_zero_mem_rationalHomSet_of_comp_self_add_smul_eq_smul` (0b434d80-afdd-599e-9405-e55a68dfba1e). -/
def S_0b434d80 : Prop :=
  ∀ {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [DecidableEq Ω] (X₁ X₂ : WeierstrassCurve Ω) [X₁.IsElliptic] [X₂.IsElliptic] (t q : ℤ) (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0) {α₁ : X₁.toAffine.Point →+ X₁.toAffine.Point} {α₂ : X₂.toAffine.Point →+ X₂.toAffine.Point} (hα₁ : α₁ ∈ WeierstrassCurve.rationalHomSet Ω X₁ X₁) (hα₂ : α₂ ∈ WeierstrassCurve.rationalHomSet Ω X₂ X₂) (h₁ : α₁.comp α₁ + q • AddMonoidHom.id _ = t • α₁) (h₂ : α₂.comp α₂ + q • AddMonoidHom.id _ = t • α₂),
    ∃ β ∈ WeierstrassCurve.rationalHomSet Ω X₁ X₂, β ≠ 0

end

section


/-- `WeierstrassCurve.exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom` (cd49331c-a1b0-51ef-9120-12c277d4bf79). -/
def S_cd49331c : Prop :=
  ∀ {L : Type*} [Field L] [IsAlgClosed L] [DecidableEq L] {A : ValuationSubring L} [DecidableEq (IsLocalRing.ResidueField A)] (E₁ E₂ : WeierstrassCurve A) (hΔ₁ : (E₁.map (IsLocalRing.residue A)).Δ ≠ 0) (hΔ₂ : (E₂.map (IsLocalRing.residue A)).Δ ≠ 0) {μ : (E₁.map A.subtype).toAffine.Point →+ (E₂.map A.subtype).toAffine.Point} (hμ : μ ∈ WeierstrassCurve.rationalHomSet L (E₁.map A.subtype) (E₂.map A.subtype)),
    ∃ ν ∈ WeierstrassCurve.rationalHomSet (IsLocalRing.ResidueField A) (E₁.map (IsLocalRing.residue A)) (E₂.map (IsLocalRing.residue A)), (WeierstrassCurve.reduceHom hΔ₂).comp μ = AddMonoidHom.comp ν (WeierstrassCurve.reduceHom hΔ₁) ∧ (μ ≠ 0 → ν ≠ 0)

end

section
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

/-- `WeierstrassCurve.mem_rationalHomSet_of_mem_rationalHomSet_baseChange_of_forall_apply_smul` (7b2524b2-5482-5a28-aa13-46652e277257). -/
def S_7b2524b2 : Prop :=
  ∀ {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) {β : (W₁⁄k).Point →+ (W₂⁄k).Point} (hβ : β ∈ WeierstrassCurve.rationalHomSet k (W₁.baseChange k) (W₂.baseChange k)) (hcomm : ∀ P : (W₁⁄k).Point, β (σ • P) = σ • β P),
    β ∈ WeierstrassCurve.rationalHomSet k W₁ W₂

end

section


/-- `WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet` (0e8f5714-9bdc-59c7-8b27-e0db105cdf99). -/
def S_0e8f5714 : Prop :=
  ∀ {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] {ρ : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point} (hρ : ρ ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) (hρ0 : ρ ≠ 0),
    ∃ σ ∈ WeierstrassCurve.rationalHomSet k W₂ W₁, ∃ n : ℤ, 0 < n ∧ AddMonoidHom.IsDualPair ρ σ n

end

section


/-- `WeierstrassCurve.surjective_of_mem_rationalHomSet` (a78cfa46-885f-5acd-8fed-e1deca0ce46e). -/
def S_a78cfa46 : Prop :=
  ∀ {F : Type*} [Field F] (k : Type*)
    [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic]
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) (hα0 : α ≠ 0),
    Function.Surjective α

end

section


/-- `WeierstrassCurve.comp_eq_comp_of_mem_rationalHomSet_of_char_nsmul_eq_zero` (094b1237-94e1-5b16-b9aa-78bd4c0515b1). -/
def S_094b1237 : Prop :=
  ∀ {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p] (W : WeierstrassCurve k) [W.IsElliptic] {T : W.toAffine.Point} (hT : T ≠ 0) (hpT : p • T = 0) {α β : W.toAffine.Point →+ W.toAffine.Point} (hα : α ∈ WeierstrassCurve.rationalHomSet k W W) (hβ : β ∈ WeierstrassCurve.rationalHomSet k W W),
    α.comp β = β.comp α

end

section


/-- `WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero` (6256914e-c202-5966-9dbb-57e96e653cbd). -/
def S_6256914e : Prop :=
  ∀ {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] {N : ℕ} (hN : (N : F) ≠ 0) {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point} (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) (hker : ∀ P : (W₁.baseChange k).toAffine.Point, (N : ℤ) • P = 0 → α P = 0),
    ∃ β ∈ WeierstrassCurve.rationalHomSet k W₁ W₂, ∀ P : (W₁.baseChange k).toAffine.Point, α P = (N : ℤ) • β P

end

section


/-- `WeierstrassCurve.comp_mem_rationalHomSet` (fe3c6240-7ff3-59e0-85b6-ee484d392077). -/
def S_fe3c6240 : Prop :=
  ∀ {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [DecidableEq k] (W₁ W₂ W₃ : WeierstrassCurve F) {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point} {β : (W₂.baseChange k).toAffine.Point →+ (W₃.baseChange k).toAffine.Point} (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) (hβ : β ∈ WeierstrassCurve.rationalHomSet k W₂ W₃),
    β.comp α ∈ WeierstrassCurve.rationalHomSet k W₁ W₃

end

section


/-- `WeierstrassCurve.add_mem_rationalHomSet` (195173b3-1093-5884-9577-aea6465f601b). -/
def S_195173b3 : Prop :=
  ∀ {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] {α β : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point} (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) (hβ : β ∈ WeierstrassCurve.rationalHomSet k W₁ W₂),
    α + β ∈ WeierstrassCurve.rationalHomSet k W₁ W₂

end

section


/-- `WeierstrassCurve.neg_mem_rationalHomSet` (580839d4-da14-5196-9d8d-0457a16f80be). -/
def S_580839d4 : Prop :=
  ∀ {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [DecidableEq k]
    (W₁ W₂ : WeierstrassCurve F)
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂),
    -α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂

end

section
open WeierstrassCurve IsLocalRing

/-- `WeierstrassCurve.exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero` (0e002459-c676-51e7-a909-d2a009b3d663). -/
def S_0e002459 : Prop :=
  ∀ {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L) [DecidableEq (ResidueField A)]
    (W : WeierstrassCurve A) (hΔ : (W.map (residue A)).Δ ≠ 0)
    {ℓ : ℕ} (hℓ : (ℓ : ResidueField A) ≠ 0)
    (Q₀ : (W.map (residue A)).toAffine.Point) (hQ₀ : ℓ • Q₀ = 0),
    ∃ Q : (W.map A.subtype).toAffine.Point, ℓ • Q = 0 ∧ reduceHom hΔ Q = Q₀

end

section


/-- `WeierstrassCurve.exists_mem_rationalHomSet_apply_eq_equivOfVariableChangeEq` (bf2cb471-43b7-5260-b4fa-a273d632e2e4). -/
def S_bf2cb471 : Prop :=
  ∀ {k : Type*} [Field k] [DecidableEq k] (W : WeierstrassCurve k) (γ : WeierstrassCurve.VariableChange k)
    {V : WeierstrassCurve k} (h : γ • W = V),
    ∃ ι ∈ WeierstrassCurve.rationalHomSet k V W, ∃ ι' ∈ WeierstrassCurve.rationalHomSet k W V,
      (∀ P : V.toAffine.Point, ι P = WeierstrassCurve.Affine.Point.equivOfVariableChangeEq h P) ∧
        ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _

end

section


/-- `WeierstrassCurve.exists_variableChange_smul_eq_and_apply_some_eq_of_comp_eq_id_of_mem_rationalHomSet` (9342fa3c-7de4-5208-bbbe-a500ee6a64ce). -/
def S_9342fa3c : Prop :=
  ∀ {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic] (u : (W.baseChange k).toAffine.Point →+ (W'.baseChange k).toAffine.Point) (hu : u ∈ WeierstrassCurve.rationalHomSet k W W') (u' : (W'.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) (hu' : u' ∈ WeierstrassCurve.rationalHomSet k W' W) (h : u'.comp u = AddMonoidHom.id ((W.baseChange k).toAffine.Point)) (h' : u.comp u' = AddMonoidHom.id ((W'.baseChange k).toAffine.Point)),
    ∃ γ : WeierstrassCurve.VariableChange F, γ • W = W' ∧ ∃ B : Set k, B.Finite ∧ ∀ (x y : k) (hxy : (W.baseChange k).toAffine.Nonsingular x y), x ∉ B → ∃ hxy', u (.some x y hxy) = .some (algebraMap F k ((γ.u⁻¹ : Fˣ) : F) ^ 2 * (x - algebraMap F k γ.r)) (algebraMap F k ((γ.u⁻¹ : Fˣ) : F) ^ 3 * (y - algebraMap F k γ.t - algebraMap F k γ.s * (x - algebraMap F k γ.r))) hxy'

end

section


/-- `WeierstrassCurve.finite_rationalHomSet_units` (97650530-fa5a-545b-844e-49617bf2c0aa). -/
def S_97650530 : Prop :=
  ∀ {F : Type*} [Field F] (k : Type*) [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic],
    {u : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point | u ∈ WeierstrassCurve.rationalHomSet k W W ∧ ∃ v ∈ WeierstrassCurve.rationalHomSet k W W, u.comp v = AddMonoidHom.id _ ∧ v.comp u = AddMonoidHom.id _}.Finite

end

section


/-- `WeierstrassCurve.exists_ne_zero_and_char_nsmul_eq_zero_of_comp_self_add_smul_eq_smul_of_dvd_of_not_dvd` (2bb50ff6-a139-5522-aa8b-e8d5fdc61ec1). -/
def S_2bb50ff6 : Prop :=
  ∀ {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p] (W : WeierstrassCurve k) [W.IsElliptic] {β : W.toAffine.Point →+ W.toAffine.Point} (hβ : β ∈ WeierstrassCurve.rationalHomSet k W W) (t q : ℤ) (hchar : β.comp β + q • AddMonoidHom.id _ = t • β) (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0) (hq : (p : ℤ) ∣ q) (ht : ¬ (p : ℤ) ∣ t),
    ∃ T : W.toAffine.Point, T ≠ 0 ∧ p • T = 0

end

end RPLib.S4T.FLT



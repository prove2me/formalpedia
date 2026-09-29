-- Prove2me | Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
-- name    : ModularCurve_FullLevelSemistableCoveringTelescope
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/806b34d8-070c-5509-8570-cf63d432e2f9
-- title:
--   Fin-indexed telescope presentation of a semistable covering
-- statement:
--   Fix a prime $q$, a positive integer $M'$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ and a finite set $W$ of places of the geometric modular function field $\mathrm{modularFunctionFieldC}(\kappa_A, M')$ over the residue field $\kappa_A = \mathrm{ResidueField}\,A$, and let $\mathcal{C}$ be a `SemistableCovering q M' A W`: a family of reduced function fields $F^{\mathrm{Ig}}_\ell$ indexed by $\ell \in \mathbb{P}^1(\mathbb{Z}/q)$ with component charts $C^{\mathrm{Ig}}_\ell$ of $\mathrm{fieldBar}\,q\,M'$ relative to $A$, fields $F^{\mathrm{ss}}_s$ with charts $C^{\mathrm{ss}}_s$ indexed by $s \in W$, annuli $\mathrm{An}_{\ell,s}$, $\mathrm{An}'_{\ell,s}$ with their attachment and partition clauses, and node places $x^{\mathrm{s}}_{\ell,s}$ on $C^{\mathrm{Ig}}_\ell$, $x^{\mathrm{t}}_{\ell,s}$ on $C^{\mathrm{ss}}_s$.
--
--   The module first packages the two families over the disjoint union $\mathbb{P}^1(\mathbb{Z}/q) \sqcup W$: `sumFbar` sends $\mathrm{inl}\,\ell$ to $F^{\mathrm{Ig}}_\ell$ and $\mathrm{inr}\,s$ to $F^{\mathrm{ss}}_s$, carrying field, $\kappa_A$-algebra and `HasPrincipalDivisors` instances and the fact that all places of these fields over $\kappa_A$ are rational; `sumChart` collects the charts and `sumNode` the node places, with $\mathrm{inl}\,\ell$ reading only the $W$-coordinate of an edge and $\mathrm{inr}\,s$ only the $\mathbb{P}^1$-coordinate. It then sets $n = \#(\mathbb{P}^1(\mathbb{Z}/q) \sqcup W)$, $m = \#(\mathbb{P}^1(\mathbb{Z}/q) \times W)$ and fixes, non-canonically, bijections $e_{\mathrm{idx}}$ onto $\mathrm{Fin}\,n$ and $e_{\mathrm{edge}} = e_{\mathrm{An}}$ onto $\mathrm{Fin}\,m$, with $e_{\mathrm{Ig}}\ell = e_{\mathrm{idx}}(\mathrm{inl}\,\ell)$ and $e_{\mathrm{SS}}s = e_{\mathrm{idx}}(\mathrm{inr}\,s)$. Reading the data back through the inverses yields the telescope: fields `teleFbar i`, charts `teleChart i`, annuli `teleAn e`, `teleAn' e`, endpoints `teleSrc e`, `teleTgt e` (always an Igusa index and a supersingular index, hence distinct) and the two node places `teleXs e`, `teleXt e`. For a parameter $\pi \in A$, `teleWidth π e` is a chosen $w \ge 1$ with $(\mathrm{teleAn}\,e).\mathrm{modulus} = u\pi^{w}$ for some unit $u$ of $A$ when such $w$ exists, and $0$ otherwise; `teleWidth_spec` records both properties under that existence hypothesis.
--
--   The remaining declarations form the dictionary between the two presentations: the equalities $\mathrm{teleFbar}(e_{\mathrm{idx}}j) = \mathrm{sumFbar}\,j$, $\mathrm{teleSrc}(e_{\mathrm{An}}(\ell,s)) = e_{\mathrm{Ig}}\ell$, $\mathrm{teleTgt}(e_{\mathrm{An}}(\ell,s)) = e_{\mathrm{SS}}s$, $\mathrm{teleAn}(e_{\mathrm{An}}(\ell,s)) = \mathrm{An}_{\ell,s}$ and its primed analogue, injectivity of $e_{\mathrm{Ig}}$ and $e_{\mathrm{SS}}$, their disjointness, the fact that every index of $\mathrm{Fin}\,n$ is of one of the two shapes, cast-free identifications of the `dom` and `integers` fields of the telescope charts with those of $C^{\mathrm{Ig}}_\ell$ and $C^{\mathrm{ss}}_s$, and the transport equivalences `forall_teleChart_iff`, `forall_teleEdge_iff`, `forall_teleEdge_idx_iff`: a property quantified over all telescope charts, respectively over all edges together with their two end charts, node places and annuli, holds if and only if it holds for the Igusa charts and the supersingular charts of $\mathcal{C}$, respectively for all pairs $(\ell,s)$.
--
--   **Relation to Mathlib.** Component charts, annuli and semistable coverings are the project's own notions; Mathlib contributes only the re-indexing device `Finite.equivFin` used to choose the enumerations of the component and edge index sets.
--
--   **Where it is used.** The telescope is the index-by-`Fin` interface through which the semistable covering of the full-level modular curve at $q$ — Igusa components, supersingular components and the annuli joining them — is fed to the generic theorems on semistable coverings used in analysing the reduction and specialisation of the Jacobian at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_FullLevelSemistableCoveringTelescope.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve.FullLevel.SemistableCovering

open AlgebraicCurve IsLocalRing

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
variable (𝒞 : SemistableCovering q M' A W)

def sumFbar : CuspidalType.ProjLine q ⊕ ↥W → Type
  | .inl ℓ => 𝒞.FIg ℓ
  | .inr s => 𝒞.FSS s

instance instFieldSumFbar : ∀ j, Field (𝒞.sumFbar j)
  | .inl ℓ => 𝒞.instFieldIg ℓ
  | .inr s => 𝒞.instFieldSS s

instance instAlgebraSumFbar : ∀ j, Algebra (ResidueField A) (𝒞.sumFbar j)
  | .inl ℓ => 𝒞.instAlgebraIg ℓ
  | .inr s => 𝒞.instAlgebraSS s

def sumChart : ∀ j, ComponentChart A (fieldBar q M') (𝒞.sumFbar j)
  | .inl ℓ => 𝒞.CIg ℓ
  | .inr s => 𝒞.CSS s

def sumNode : ∀ j, CuspidalType.ProjLine q × ↥W → Place (ResidueField A) (𝒞.sumFbar j)
  | .inl ℓ => fun p => 𝒞.xs ℓ p.2
  | .inr s => fun p => 𝒞.xt p.1 s

instance instHasPrincipalDivisorsSumFbar : ∀ j, HasPrincipalDivisors (ResidueField A) (𝒞.sumFbar j)
  | .inl ℓ => 𝒞.hasPrincipalDivisors_Ig ℓ
  | .inr s => 𝒞.hasPrincipalDivisors_SS s

theorem isRational_sumFbar : ∀ j (x : Place (ResidueField A) (𝒞.sumFbar j)), x.IsRational
  | .inl ℓ, x => 𝒞.isRational_Ig ℓ x
  | .inr s, x => 𝒞.isRational_SS s x

@[simp] theorem sumChart_inl (ℓ : CuspidalType.ProjLine q) : 𝒞.sumChart (Sum.inl ℓ) = 𝒞.CIg ℓ := rfl
@[simp] theorem sumChart_inr (s : ↥W) : 𝒞.sumChart (Sum.inr s) = 𝒞.CSS s := rfl
@[simp] theorem sumNode_inl (ℓ : CuspidalType.ProjLine q) (p : CuspidalType.ProjLine q × ↥W) :
    𝒞.sumNode (Sum.inl ℓ) p = 𝒞.xs ℓ p.2 := rfl
@[simp] theorem sumNode_inr (s : ↥W) (p : CuspidalType.ProjLine q × ↥W) :
    𝒞.sumNode (Sum.inr s) p = 𝒞.xt p.1 s := rfl
theorem sumFbar_inl (ℓ : CuspidalType.ProjLine q) : 𝒞.sumFbar (Sum.inl ℓ) = 𝒞.FIg ℓ := rfl
theorem sumFbar_inr (s : ↥W) : 𝒞.sumFbar (Sum.inr s) = 𝒞.FSS s := rfl

abbrev teleN (_𝒞 : SemistableCovering q M' A W) : ℕ := Nat.card (CuspidalType.ProjLine q ⊕ ↥W)

abbrev teleM (_𝒞 : SemistableCovering q M' A W) : ℕ := Nat.card (CuspidalType.ProjLine q × ↥W)

def eIdx (𝒞 : SemistableCovering q M' A W) : CuspidalType.ProjLine q ⊕ ↥W ≃ Fin 𝒞.teleN := Finite.equivFin _

def eEdge (𝒞 : SemistableCovering q M' A W) : CuspidalType.ProjLine q × ↥W ≃ Fin 𝒞.teleM := Finite.equivFin _

def eIg (𝒞 : SemistableCovering q M' A W) (ℓ : CuspidalType.ProjLine q) : Fin 𝒞.teleN := 𝒞.eIdx (Sum.inl ℓ)

def eSS (𝒞 : SemistableCovering q M' A W) (s : ↥W) : Fin 𝒞.teleN := 𝒞.eIdx (Sum.inr s)

abbrev eAn (𝒞 : SemistableCovering q M' A W) : CuspidalType.ProjLine q × ↥W ≃ Fin 𝒞.teleM := 𝒞.eEdge

def teleFbar (i : Fin 𝒞.teleN) : Type := 𝒞.sumFbar (𝒞.eIdx.symm i)

instance instFieldTeleFbar (i : Fin 𝒞.teleN) : Field (𝒞.teleFbar i) := 𝒞.instFieldSumFbar _
instance instAlgebraTeleFbar (i : Fin 𝒞.teleN) : Algebra (ResidueField A) (𝒞.teleFbar i) := 𝒞.instAlgebraSumFbar _
instance instHasPrincipalDivisorsTeleFbar (i : Fin 𝒞.teleN) :
    HasPrincipalDivisors (ResidueField A) (𝒞.teleFbar i) := 𝒞.instHasPrincipalDivisorsSumFbar _

theorem isRational_teleFbar (i : Fin 𝒞.teleN) (x : Place (ResidueField A) (𝒞.teleFbar i)) : x.IsRational :=
  𝒞.isRational_sumFbar _ x

def teleChart (i : Fin 𝒞.teleN) : ComponentChart A (fieldBar q M') (𝒞.teleFbar i) := 𝒞.sumChart (𝒞.eIdx.symm i)

def teleAn (e : Fin 𝒞.teleM) : Annulus A (fieldBar q M') := 𝒞.An (𝒞.eEdge.symm e).1 (𝒞.eEdge.symm e).2

def teleAn' (e : Fin 𝒞.teleM) : Annulus A (fieldBar q M') := 𝒞.An' (𝒞.eEdge.symm e).1 (𝒞.eEdge.symm e).2

def teleWidth (π : A) (e : Fin 𝒞.teleM) : ℕ := by
  classical
  exact if h : ∃ w : ℕ, 1 ≤ w ∧ ∃ u : Aˣ, (𝒞.teleAn e).modulus = u * π ^ w then h.choose else 0

theorem teleWidth_spec (π : A) (e : Fin 𝒞.teleM) (h : ∃ w : ℕ, 1 ≤ w ∧ ∃ u : Aˣ, (𝒞.teleAn e).modulus = u * π ^ w) :
    1 ≤ 𝒞.teleWidth π e ∧ ∃ u : Aˣ, (𝒞.teleAn e).modulus = u * π ^ 𝒞.teleWidth π e := by
  classical
  have : 𝒞.teleWidth π e = h.choose := by unfold teleWidth; exact dif_pos h
  rw [this]; exact h.choose_spec

def teleSrc (e : Fin 𝒞.teleM) : Fin 𝒞.teleN := 𝒞.eIdx (Sum.inl (𝒞.eEdge.symm e).1)

def teleTgt (e : Fin 𝒞.teleM) : Fin 𝒞.teleN := 𝒞.eIdx (Sum.inr (𝒞.eEdge.symm e).2)

def teleXs (e : Fin 𝒞.teleM) : Place (ResidueField A) (𝒞.teleFbar (𝒞.teleSrc e)) :=
  𝒞.sumNode (𝒞.eIdx.symm (𝒞.eIdx (Sum.inl (𝒞.eEdge.symm e).1))) (𝒞.eEdge.symm e)

def teleXt (e : Fin 𝒞.teleM) : Place (ResidueField A) (𝒞.teleFbar (𝒞.teleTgt e)) :=
  𝒞.sumNode (𝒞.eIdx.symm (𝒞.eIdx (Sum.inr (𝒞.eEdge.symm e).2))) (𝒞.eEdge.symm e)

theorem teleFbar_def (i : Fin 𝒞.teleN) : 𝒞.teleFbar i = 𝒞.sumFbar (𝒞.eIdx.symm i) := rfl
theorem teleChart_def (i : Fin 𝒞.teleN) : 𝒞.teleChart i = 𝒞.sumChart (𝒞.eIdx.symm i) := rfl
theorem teleFbar_eIdx (j : CuspidalType.ProjLine q ⊕ ↥W) : 𝒞.teleFbar (𝒞.eIdx j) = 𝒞.sumFbar j := by
  rw [teleFbar_def, Equiv.symm_apply_apply]

@[simp] theorem teleSrc_eEdge (ℓ : CuspidalType.ProjLine q) (s : ↥W) :
    𝒞.teleSrc (𝒞.eEdge (ℓ, s)) = 𝒞.eIdx (Sum.inl ℓ) := by simp [teleSrc]
@[simp] theorem teleTgt_eEdge (ℓ : CuspidalType.ProjLine q) (s : ↥W) :
    𝒞.teleTgt (𝒞.eEdge (ℓ, s)) = 𝒞.eIdx (Sum.inr s) := by simp [teleTgt]
@[simp] theorem teleAn_eEdge (ℓ : CuspidalType.ProjLine q) (s : ↥W) : 𝒞.teleAn (𝒞.eEdge (ℓ, s)) = 𝒞.An ℓ s := by
  simp [teleAn]
@[simp] theorem teleAn'_eEdge (ℓ : CuspidalType.ProjLine q) (s : ↥W) : 𝒞.teleAn' (𝒞.eEdge (ℓ, s)) = 𝒞.An' ℓ s := by
  simp [teleAn']
theorem eIdx_symm_teleSrc (e : Fin 𝒞.teleM) : 𝒞.eIdx.symm (𝒞.teleSrc e) = Sum.inl (𝒞.eEdge.symm e).1 := by
  simp [teleSrc]
theorem eIdx_symm_teleTgt (e : Fin 𝒞.teleM) : 𝒞.eIdx.symm (𝒞.teleTgt e) = Sum.inr (𝒞.eEdge.symm e).2 := by
  simp [teleTgt]

@[simp] theorem eIdx_symm_eIg (ℓ : CuspidalType.ProjLine q) : 𝒞.eIdx.symm (𝒞.eIg ℓ) = Sum.inl ℓ := by simp [eIg]
@[simp] theorem eIdx_symm_eSS (s : ↥W) : 𝒞.eIdx.symm (𝒞.eSS s) = Sum.inr s := by simp [eSS]
@[simp] theorem teleSrc_eAn (ℓ : CuspidalType.ProjLine q) (s : ↥W) : 𝒞.teleSrc (𝒞.eAn (ℓ, s)) = 𝒞.eIg ℓ :=
  𝒞.teleSrc_eEdge ℓ s
@[simp] theorem teleTgt_eAn (ℓ : CuspidalType.ProjLine q) (s : ↥W) : 𝒞.teleTgt (𝒞.eAn (ℓ, s)) = 𝒞.eSS s :=
  𝒞.teleTgt_eEdge ℓ s
theorem teleSrc_eq_eIg (e : Fin 𝒞.teleM) : 𝒞.teleSrc e = 𝒞.eIg (𝒞.eAn.symm e).1 := rfl
theorem teleTgt_eq_eSS (e : Fin 𝒞.teleM) : 𝒞.teleTgt e = 𝒞.eSS (𝒞.eAn.symm e).2 := rfl
theorem teleFbar_eIg (ℓ : CuspidalType.ProjLine q) : 𝒞.teleFbar (𝒞.eIg ℓ) = 𝒞.FIg ℓ := 𝒞.teleFbar_eIdx _
theorem teleFbar_eSS (s : ↥W) : 𝒞.teleFbar (𝒞.eSS s) = 𝒞.FSS s := 𝒞.teleFbar_eIdx _
theorem eIg_ne_eSS (ℓ : CuspidalType.ProjLine q) (s : ↥W) : 𝒞.eIg ℓ ≠ 𝒞.eSS s := fun h =>
  Sum.inl_ne_inr (𝒞.eIdx.injective h)
theorem eIg_injective : Function.Injective 𝒞.eIg := fun _ _ h => Sum.inl_injective (𝒞.eIdx.injective h)
theorem eSS_injective : Function.Injective 𝒞.eSS := fun _ _ h => Sum.inr_injective (𝒞.eIdx.injective h)
theorem eIg_or_eSS (i : Fin 𝒞.teleN) : (∃ ℓ, i = 𝒞.eIg ℓ) ∨ ∃ s, i = 𝒞.eSS s := by
  rcases h : 𝒞.eIdx.symm i with ℓ | s
  · exact Or.inl ⟨ℓ, by rw [eIg, ← h, Equiv.apply_symm_apply]⟩
  · exact Or.inr ⟨s, by rw [eSS, ← h, Equiv.apply_symm_apply]⟩

theorem teleSrc_ne_teleTgt (e : Fin 𝒞.teleM) : 𝒞.teleSrc e ≠ 𝒞.teleTgt e := fun h =>
  Sum.inl_ne_inr (𝒞.eIdx.injective h)

theorem teleChart_eIdx_iff (P : ∀ j : CuspidalType.ProjLine q ⊕ ↥W, ComponentChart A (fieldBar q M') (𝒞.sumFbar j) → Prop)
    (j : CuspidalType.ProjLine q ⊕ ↥W) :
    P (𝒞.eIdx.symm (𝒞.eIdx j)) (𝒞.teleChart (𝒞.eIdx j)) ↔ P j (𝒞.sumChart j) := by
  rw [teleChart_def, Equiv.symm_apply_apply]

theorem teleChart_sumNode_eIdx_iff
    (P : ∀ j : CuspidalType.ProjLine q ⊕ ↥W, ComponentChart A (fieldBar q M') (𝒞.sumFbar j) →
      Place (ResidueField A) (𝒞.sumFbar j) → Prop)
    (j : CuspidalType.ProjLine q ⊕ ↥W) (p : CuspidalType.ProjLine q × ↥W) :
    P (𝒞.eIdx.symm (𝒞.eIdx j)) (𝒞.teleChart (𝒞.eIdx j)) (𝒞.sumNode (𝒞.eIdx.symm (𝒞.eIdx j)) p) ↔
      P j (𝒞.sumChart j) (𝒞.sumNode j p) := by
  rw [teleChart_def, Equiv.symm_apply_apply]

theorem teleChart_eIdx_dom (j : CuspidalType.ProjLine q ⊕ ↥W) : (𝒞.teleChart (𝒞.eIdx j)).dom = (𝒞.sumChart j).dom :=
  (𝒞.teleChart_eIdx_iff (fun _ C => C.dom = (𝒞.sumChart j).dom) j).2 rfl
theorem teleChart_eIdx_integers (j : CuspidalType.ProjLine q ⊕ ↥W) :
    (𝒞.teleChart (𝒞.eIdx j)).integers = (𝒞.sumChart j).integers :=
  (𝒞.teleChart_eIdx_iff (fun _ C => C.integers = (𝒞.sumChart j).integers) j).2 rfl

theorem teleChart_eIg_dom (ℓ : CuspidalType.ProjLine q) : (𝒞.teleChart (𝒞.eIg ℓ)).dom = (𝒞.CIg ℓ).dom :=
  𝒞.teleChart_eIdx_dom _
theorem teleChart_eSS_dom (s : ↥W) : (𝒞.teleChart (𝒞.eSS s)).dom = (𝒞.CSS s).dom := 𝒞.teleChart_eIdx_dom _
theorem teleChart_eIg_integers (ℓ : CuspidalType.ProjLine q) : (𝒞.teleChart (𝒞.eIg ℓ)).integers = (𝒞.CIg ℓ).integers :=
  𝒞.teleChart_eIdx_integers _
theorem teleChart_eSS_integers (s : ↥W) : (𝒞.teleChart (𝒞.eSS s)).integers = (𝒞.CSS s).integers :=
  𝒞.teleChart_eIdx_integers _

theorem forall_teleChart_iff
    (Q : ∀ (F : Type) [Field F] [Algebra (ResidueField A) F], ComponentChart A (fieldBar q M') F → Prop) :
    (∀ i, Q (𝒞.teleFbar i) (𝒞.teleChart i)) ↔ (∀ ℓ, Q (𝒞.FIg ℓ) (𝒞.CIg ℓ)) ∧ ∀ s, Q (𝒞.FSS s) (𝒞.CSS s) := by
  constructor
  · intro h
    refine ⟨fun ℓ => ?_, fun s => ?_⟩
    · have := h (𝒞.eIg ℓ)
      exact (𝒞.teleChart_eIdx_iff (fun j C => Q (𝒞.sumFbar j) C) (Sum.inl ℓ)).1 this
    · have := h (𝒞.eSS s)
      exact (𝒞.teleChart_eIdx_iff (fun j C => Q (𝒞.sumFbar j) C) (Sum.inr s)).1 this
  · rintro ⟨hI, hS⟩ i
    show Q (𝒞.sumFbar (𝒞.eIdx.symm i)) (𝒞.sumChart (𝒞.eIdx.symm i))
    rcases 𝒞.eIdx.symm i with ℓ | s
    · exact hI ℓ
    · exact hS s

theorem forall_teleEdge_iff
    (R : ∀ (F₁ F₂ : Type) [Field F₁] [Algebra (ResidueField A) F₁] [Field F₂] [Algebra (ResidueField A) F₂],
      ComponentChart A (fieldBar q M') F₁ → Place (ResidueField A) F₁ →
        ComponentChart A (fieldBar q M') F₂ → Place (ResidueField A) F₂ →
        Annulus A (fieldBar q M') → Annulus A (fieldBar q M') → Prop) :
    (∀ e, R _ _ (𝒞.teleChart (𝒞.teleSrc e)) (𝒞.teleXs e) (𝒞.teleChart (𝒞.teleTgt e)) (𝒞.teleXt e)
        (𝒞.teleAn e) (𝒞.teleAn' e)) ↔
      ∀ ℓ s, R _ _ (𝒞.CIg ℓ) (𝒞.xs ℓ s) (𝒞.CSS s) (𝒞.xt ℓ s) (𝒞.An ℓ s) (𝒞.An' ℓ s) := by

  have key : ∀ p : CuspidalType.ProjLine q × ↥W,
      R _ _ (𝒞.sumChart (𝒞.eIdx.symm (𝒞.eIdx (Sum.inl p.1)))) (𝒞.sumNode (𝒞.eIdx.symm (𝒞.eIdx (Sum.inl p.1))) p)
          (𝒞.sumChart (𝒞.eIdx.symm (𝒞.eIdx (Sum.inr p.2)))) (𝒞.sumNode (𝒞.eIdx.symm (𝒞.eIdx (Sum.inr p.2))) p)
          (𝒞.An p.1 p.2) (𝒞.An' p.1 p.2) ↔
        R _ _ (𝒞.CIg p.1) (𝒞.xs p.1 p.2) (𝒞.CSS p.2) (𝒞.xt p.1 p.2) (𝒞.An p.1 p.2) (𝒞.An' p.1 p.2) := by
    intro p
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  have tele : ∀ e, R _ _ (𝒞.teleChart (𝒞.teleSrc e)) (𝒞.teleXs e) (𝒞.teleChart (𝒞.teleTgt e)) (𝒞.teleXt e)
        (𝒞.teleAn e) (𝒞.teleAn' e) ↔
      (fun p : CuspidalType.ProjLine q × ↥W =>
        R _ _ (𝒞.sumChart (𝒞.eIdx.symm (𝒞.eIdx (Sum.inl p.1)))) (𝒞.sumNode (𝒞.eIdx.symm (𝒞.eIdx (Sum.inl p.1))) p)
          (𝒞.sumChart (𝒞.eIdx.symm (𝒞.eIdx (Sum.inr p.2)))) (𝒞.sumNode (𝒞.eIdx.symm (𝒞.eIdx (Sum.inr p.2))) p)
          (𝒞.An p.1 p.2) (𝒞.An' p.1 p.2)) (𝒞.eEdge.symm e) := fun _ => Iff.rfl
  constructor
  · intro h ℓ s
    have h1 := (tele _).1 (h (𝒞.eEdge (ℓ, s)))
    rw [Equiv.symm_apply_apply] at h1
    exact (key (ℓ, s)).1 h1
  · intro h e
    exact (tele e).2 ((key (𝒞.eEdge.symm e)).2 (h _ _))

theorem forall_teleEdge_idx_iff
    (R : ∀ (F₁ F₂ : Type) [Field F₁] [Algebra (ResidueField A) F₁] [Field F₂] [Algebra (ResidueField A) F₂],
      Fin 𝒞.teleN → Fin 𝒞.teleN → ComponentChart A (fieldBar q M') F₁ → Place (ResidueField A) F₁ →
        ComponentChart A (fieldBar q M') F₂ → Place (ResidueField A) F₂ →
        Annulus A (fieldBar q M') → Annulus A (fieldBar q M') → Prop) :
    (∀ e, R _ _ (𝒞.teleSrc e) (𝒞.teleTgt e) (𝒞.teleChart (𝒞.teleSrc e)) (𝒞.teleXs e)
        (𝒞.teleChart (𝒞.teleTgt e)) (𝒞.teleXt e) (𝒞.teleAn e) (𝒞.teleAn' e)) ↔
      ∀ ℓ s, R _ _ (𝒞.eIg ℓ) (𝒞.eSS s) (𝒞.CIg ℓ) (𝒞.xs ℓ s) (𝒞.CSS s) (𝒞.xt ℓ s) (𝒞.An ℓ s) (𝒞.An' ℓ s) := by
  have key : ∀ p : CuspidalType.ProjLine q × ↥W,
      R _ _ (𝒞.eIg p.1) (𝒞.eSS p.2)
          (𝒞.sumChart (𝒞.eIdx.symm (𝒞.eIdx (Sum.inl p.1)))) (𝒞.sumNode (𝒞.eIdx.symm (𝒞.eIdx (Sum.inl p.1))) p)
          (𝒞.sumChart (𝒞.eIdx.symm (𝒞.eIdx (Sum.inr p.2)))) (𝒞.sumNode (𝒞.eIdx.symm (𝒞.eIdx (Sum.inr p.2))) p)
          (𝒞.An p.1 p.2) (𝒞.An' p.1 p.2) ↔
        R _ _ (𝒞.eIg p.1) (𝒞.eSS p.2) (𝒞.CIg p.1) (𝒞.xs p.1 p.2) (𝒞.CSS p.2) (𝒞.xt p.1 p.2)
          (𝒞.An p.1 p.2) (𝒞.An' p.1 p.2) := by
    intro p
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  have tele : ∀ e, R _ _ (𝒞.teleSrc e) (𝒞.teleTgt e) (𝒞.teleChart (𝒞.teleSrc e)) (𝒞.teleXs e)
        (𝒞.teleChart (𝒞.teleTgt e)) (𝒞.teleXt e) (𝒞.teleAn e) (𝒞.teleAn' e) ↔
      (fun p : CuspidalType.ProjLine q × ↥W =>
        R _ _ (𝒞.eIg p.1) (𝒞.eSS p.2)
          (𝒞.sumChart (𝒞.eIdx.symm (𝒞.eIdx (Sum.inl p.1)))) (𝒞.sumNode (𝒞.eIdx.symm (𝒞.eIdx (Sum.inl p.1))) p)
          (𝒞.sumChart (𝒞.eIdx.symm (𝒞.eIdx (Sum.inr p.2)))) (𝒞.sumNode (𝒞.eIdx.symm (𝒞.eIdx (Sum.inr p.2))) p)
          (𝒞.An p.1 p.2) (𝒞.An' p.1 p.2)) (𝒞.eEdge.symm e) := fun _ => Iff.rfl
  constructor
  · intro h ℓ s
    have h1 := (tele _).1 (h (𝒞.eEdge (ℓ, s)))
    rw [Equiv.symm_apply_apply] at h1
    exact (key (ℓ, s)).1 h1
  · intro h e
    exact (tele e).2 ((key (𝒞.eEdge.symm e)).2 (h _ _))

example (s : ↥W) : (𝒞.teleChart (𝒞.eSS s)).integers = (𝒞.CSS s).integers ∧ (𝒞.teleChart (𝒞.eSS s)).dom = (𝒞.CSS s).dom :=
  ⟨𝒞.teleChart_eSS_integers s, 𝒞.teleChart_eSS_dom s⟩

example (Q : ∀ (F : Type) [Field F] [Algebra (ResidueField A) F], ComponentChart A (fieldBar q M') F → Prop)
    (hI : ∀ ℓ, Q _ (𝒞.CIg ℓ)) (hS : ∀ s, Q _ (𝒞.CSS s)) (i : Fin 𝒞.teleN) : Q _ (𝒞.teleChart i) :=
  (𝒞.forall_teleChart_iff Q).2 ⟨hI, hS⟩ i

end ModularCurve.FullLevel.SemistableCovering

end



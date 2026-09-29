-- Prove2me | Definitions.Def_MvFormalGroup_OfFormalGroupV2
-- name    : MvFormalGroup_OfFormalGroupV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/169cbc44-adb4-551c-a6d8-72df19d747a3
-- title:
--   One-dimensional formal group laws as multivariate formal groups
-- statement:
--   Over a commutative ring $R$, this module identifies Mathlib's one-variable formal group laws with the project's $1$-dimensional multivariate formal groups. The index dictionary is given by the embeddings `e2 : Fin 2 ↪ Fin 1 ⊕ Fin 1` (sending $0,1$ to `Sum.inl 0`, `Sum.inr 0`), `e3 : Fin 3 ↪ Fin 1 ⊕ (Fin 1 ⊕ Fin 1)` and `e1 : Unit ↪ Fin 1`, together with two transport lemmas stating that `subst` along a family commutes with `rename` along an embedding (in either order) when the substituted family has the substitutability property `HasSubst`. Given `F : FormalGroup R`, `ofFormalGroup F : MvFormalGroup 1 R` has as its single power series the renaming of $F(X,Y)$ along `e2`; the four structure fields (vanishing constant term, the two linear coefficients being $1$, and associativity in three variables, the last obtained from $F$'s associativity by renaming along `e3`) are established as part of the definition. `coeff_ofFormalGroup` records that the coefficient of $X^a Y^b$ is unchanged, and commutativity of $F$ is transferred to the `IsComm` instance for `ofFormalGroup F`. A further group of lemmas sets up the single-variable dictionary: `toMv` is renaming $R[[Z]] \to R[[X_0]]$ along `e1`, `ofMv` is the inverse `killCompl`, and their coefficient, constant-term, $X$, zero, substitutability and linear-part behaviour is recorded (the linear part of the one-term family `toMv s` being $\operatorname{coeff}_1(s)$ times the $1\times 1$ identity matrix). Also proved: [`MvFormalGroup`](../def/MvFormalGroup_BasicV2.html#L15) equality is detected by the power-series family; `ofFormalGroup` commutes with base change along a ring homomorphism; the $n$-series of `ofFormalGroup F` is the constant family `toMv (F.nthSeries n)`; and the one-variable homomorphism identity for $s$ with zero constant term is equivalent to the `Hom` identity for `toMv s`, whence the two constructions [`FormalGroup.LawHom.toMvHom`](../def/MvFormalGroup_OfFormalGroupV2.html#L355) and [`FormalGroup.LawHom.ofMvHom`](../def/MvFormalGroup_OfFormalGroupV2.html#L364) passing between `LawHom F G` and `Hom (ofFormalGroup F) (ofFormalGroup G)`.
--
--   **Relation to Mathlib.** `FormalGroup R` and its `IsComm` class, together with `rename`, `killCompl` and `subst` for multivariate power series, are Mathlib's; the structures [`MvFormalGroup g R`](../def/MvFormalGroup_BasicV2.html#L15), [`MvFormalGroup.Hom`](../def/MvFormalGroup_BasicV2.html#L71), [`FormalGroup.LawHom`](../def/FormalGroup_PointTransport.html#L15) and the $n$-series used here are the project's own definitions.
--
--   **Where it is used.** The dictionary lets statements proved for multivariate formal groups (their $n$-series, linear parts, homomorphisms and base change) be applied to one-dimensional formal group laws, such as Lubin–Tate groups and formal groups attached to elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvFormalGroup_OfFormalGroupV2.lean

import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_PointTransport
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.RingTheory.MvPowerSeries.Rename

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {R : Type*} [CommRing R]

def e2 : Fin 2 ↪ Fin 1 ⊕ Fin 1 :=
  ⟨![Sum.inl 0, Sum.inr 0], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

@[simp] theorem e2_zero : e2 0 = Sum.inl 0 := rfl

@[simp] theorem e2_one : e2 1 = Sum.inr 0 := rfl

def e3 : Fin 3 ↪ Fin 1 ⊕ (Fin 1 ⊕ Fin 1) :=
  ⟨![Sum.inl 0, Sum.inr (Sum.inl 0), Sum.inr (Sum.inr 0)], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

@[simp] theorem e3_zero : e3 0 = Sum.inl 0 := rfl

@[simp] theorem e3_one : e3 1 = Sum.inr (Sum.inl 0) := rfl

@[simp] theorem e3_two : e3 2 = Sum.inr (Sum.inr 0) := rfl

theorem subst_rename {σ τ υ : Type*} (e : σ ↪ τ) {a : τ → MvPowerSeries υ R}
    (ha : HasSubst a) (f : MvPowerSeries σ R) :
    subst a (rename e f) = subst (fun s => a (e s)) f := by
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) ha]
  congr 1
  funext s
  exact subst_X ha (e s)

theorem rename_subst {σ τ υ : Type*} (e : τ ↪ υ) {a : σ → MvPowerSeries τ R}
    (ha : HasSubst a) (f : MvPowerSeries σ R) :
    rename e (subst a f) = subst (fun s => rename e (a s)) f := by
  rw [rename_eq_subst, subst_comp_subst_apply ha (HasSubst.X_comp _)]
  congr 1
  funext s
  exact (rename_eq_subst _ (a s)).symm

def ofFormalGroup (F : FormalGroup R) : MvFormalGroup 1 R where
  toPowerSeries := fun _ => rename e2 F.toPowerSeries
  constantCoeff_eq_zero := fun _ => by rw [constantCoeff_rename, F.zero_constantCoeff]
  coeff_single_inl := by
    intro i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0, if_pos rfl,
      show Finsupp.single (Sum.inl (0 : Fin 1)) 1 = Finsupp.embDomain e2 (Finsupp.single 0 1) by
        rw [Finsupp.embDomain_single]; rfl,
      coeff_embDomain_rename]
    exact F.lin_coeff_X
  coeff_single_inr := by
    intro i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0, if_pos rfl,
      show Finsupp.single (Sum.inr (0 : Fin 1)) 1 = Finsupp.embDomain e2 (Finsupp.single 1 1) by
        rw [Finsupp.embDomain_single]; rfl,
      coeff_embDomain_rename]
    exact F.lin_coeff_Y
  assoc := by
    intro i

    have c0 : ∀ a b : Fin 3, MvPowerSeries.constantCoeff
        (subst (![X a, X b] : Fin 2 → MvPowerSeries (Fin 3) R) F.toPowerSeries) = 0 :=
      fun a b => constantCoeff_subst_eq_zero HasSubst.X_X
        (Fin.forall_fin_two.mpr ⟨constantCoeff_X _, constantCoeff_X _⟩) F.zero_constantCoeff
    have hL : HasSubst (![subst ![X 0, X 1] F.toPowerSeries, X 2] :
        Fin 2 → MvPowerSeries (Fin 3) R) :=
      hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨c0 0 1, constantCoeff_X _⟩)
    have hR : HasSubst (![X 0, subst ![X 1, X 2] F.toPowerSeries] :
        Fin 2 → MvPowerSeries (Fin 3) R) :=
      hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨constantCoeff_X _, c0 1 2⟩)

    have hB : HasSubst (Sum.elim
        (fun l : Fin 1 => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
        fun l => X (Sum.inr (Sum.inl l))) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with l | l <;> simp
    have hC : HasSubst (Sum.elim
        (fun l : Fin 1 => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
        fun l => X (Sum.inr (Sum.inr l))) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with l | l <;> simp
    have hB2 : HasSubst (fun s : Fin 2 => Sum.elim
        (fun l : Fin 1 => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
        (fun l => X (Sum.inr (Sum.inl l))) (e2 s)) :=
      hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨constantCoeff_X _, constantCoeff_X _⟩)
    have hC2 : HasSubst (fun s : Fin 2 => Sum.elim
        (fun l : Fin 1 => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
        (fun l => X (Sum.inr (Sum.inr l))) (e2 s)) :=
      hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨constantCoeff_X _, constantCoeff_X _⟩)
    rw [subst_rename e2 hB, subst_rename e2 hC]
    have hA₁ : HasSubst (Sum.elim
        (fun _ : Fin 1 => subst (fun s : Fin 2 => Sum.elim
          (fun l : Fin 1 => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
          (fun l => X (Sum.inr (Sum.inl l))) (e2 s)) F.toPowerSeries)
        fun j => X (Sum.inr (Sum.inr j))) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j)
      · exact constantCoeff_subst_eq_zero hB2
          (Fin.forall_fin_two.mpr ⟨constantCoeff_X _, constantCoeff_X _⟩) F.zero_constantCoeff
      · exact constantCoeff_X _
    have hA₂ : HasSubst (Sum.elim
        (fun j : Fin 1 => (X (Sum.inl j) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
        fun _ : Fin 1 => subst (fun s : Fin 2 => Sum.elim
          (fun l : Fin 1 => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
          (fun l => X (Sum.inr (Sum.inr l))) (e2 s)) F.toPowerSeries) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j)
      · exact constantCoeff_X _
      · exact constantCoeff_subst_eq_zero hC2
          (Fin.forall_fin_two.mpr ⟨constantCoeff_X _, constantCoeff_X _⟩) F.zero_constantCoeff
    rw [subst_rename e2 hA₁, subst_rename e2 hA₂]

    have eL : (fun s : Fin 2 => Sum.elim
        (fun _ : Fin 1 => subst (fun s : Fin 2 => Sum.elim
          (fun l : Fin 1 => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
          (fun l => X (Sum.inr (Sum.inl l))) (e2 s)) F.toPowerSeries)
        (fun j => X (Sum.inr (Sum.inr j))) (e2 s))
        = fun s => rename e3 ((![subst ![X 0, X 1] F.toPowerSeries, X 2] :
            Fin 2 → MvPowerSeries (Fin 3) R) s) := by
      refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
      · rw [e2_zero, Sum.elim_inl, Matrix.cons_val_zero, rename_subst _ HasSubst.X_X]
        refine congrArg (fun a => subst a F.toPowerSeries) ?_
        refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
        · rw [e2_zero, Sum.elim_inl, Matrix.cons_val_zero, rename_X, e3_zero]
        · rw [e2_one, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero, rename_X, e3_one]
      · rw [e2_one, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero, rename_X, e3_two]
    have eR : (fun s : Fin 2 => Sum.elim
        (fun j : Fin 1 => (X (Sum.inl j) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
        (fun _ => subst (fun s : Fin 2 => Sum.elim
          (fun l : Fin 1 => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) R))
          (fun l => X (Sum.inr (Sum.inr l))) (e2 s)) F.toPowerSeries) (e2 s))
        = fun s => rename e3 ((![X 0, subst ![X 1, X 2] F.toPowerSeries] :
            Fin 2 → MvPowerSeries (Fin 3) R) s) := by
      refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
      · rw [e2_zero, Sum.elim_inl, Matrix.cons_val_zero, rename_X, e3_zero]
      · rw [e2_one, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero,
          rename_subst _ HasSubst.X_X]
        refine congrArg (fun a => subst a F.toPowerSeries) ?_
        refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
        · rw [e2_zero, Sum.elim_inl, Matrix.cons_val_zero, rename_X, e3_one]
        · rw [e2_one, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero, rename_X, e3_two]
    rw [eL, eR, ← rename_subst e3 hL, ← rename_subst e3 hR]
    exact congrArg (rename e3) F.assoc

theorem coeff_ofFormalGroup (F : FormalGroup R) (a b : ℕ) (i : Fin 1) :
    coeff (Finsupp.single (Sum.inl 0) a + Finsupp.single (Sum.inr 0) b)
        ((ofFormalGroup F).toPowerSeries i)
      = coeff (Finsupp.single 0 a + Finsupp.single 1 b) F.toPowerSeries := by
  rw [show Finsupp.single (Sum.inl (0 : Fin 1)) a + Finsupp.single (Sum.inr (0 : Fin 1)) b
      = Finsupp.embDomain e2 (Finsupp.single 0 a + Finsupp.single 1 b) by
    rw [Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single]; rfl]
  exact coeff_embDomain_rename e2 F.toPowerSeries _

instance instIsCommOfFormalGroup (F : FormalGroup R) [F.IsComm] : (ofFormalGroup F).IsComm where
  comm := by
    intro i
    show subst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin 1 ⊕ Fin 1) R))
        fun j => X (Sum.inl j)) (rename e2 F.toPowerSeries) = rename e2 F.toPowerSeries
    have hs : HasSubst (Sum.elim
        (fun j : Fin 1 => (X (Sum.inr j) : MvPowerSeries (Fin 1 ⊕ Fin 1) R))
        fun j => X (Sum.inl j)) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with l | l <;> simp
    rw [subst_rename e2 hs]
    calc subst (fun s => Sum.elim
            (fun j : Fin 1 => (X (Sum.inr j) : MvPowerSeries (Fin 1 ⊕ Fin 1) R))
            (fun j => X (Sum.inl j)) (e2 s)) F.toPowerSeries
        = subst (fun s => rename e2 ((![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) R) s))
            F.toPowerSeries := by
          refine congrArg (fun a => subst a F.toPowerSeries) ?_
          refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
          · rw [e2_zero, Sum.elim_inl, Matrix.cons_val_zero, rename_X, e2_one]
          · rw [e2_one, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero, rename_X,
              e2_zero]
      _ = rename e2 (subst ![X 1, X 0] F.toPowerSeries) :=
          (rename_subst e2 HasSubst.X_X F.toPowerSeries).symm
      _ = rename e2 F.toPowerSeries :=
          congrArg (rename e2) (FormalGroup.IsComm.comm (F := F)).symm

theorem eq_of_toPowerSeries_eq {g : ℕ} : ∀ {F G : MvFormalGroup g R}, F.toPowerSeries = G.toPowerSeries → F = G
  | ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, rfl => rfl

def e1 : Unit ↪ Fin 1 := ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩

@[simp] theorem e1_apply (u : Unit) : e1 u = 0 := rfl

def toMv (s : PowerSeries R) : MvPowerSeries (Fin 1) R := rename e1 s

def ofMv (t : MvPowerSeries (Fin 1) R) : PowerSeries R := killCompl e1 t

theorem toMv_def (s : PowerSeries R) : toMv s = rename e1 s := rfl

theorem ofMv_toMv (s : PowerSeries R) : ofMv (toMv s) = s := killCompl_rename_app s

theorem single_zero_eq_embDomain (n : ℕ) :
    Finsupp.single (0 : Fin 1) n = Finsupp.embDomain e1 (Finsupp.single () n) := by
  rw [Finsupp.embDomain_single]; rfl

theorem coeff_toMv (s : PowerSeries R) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) n) (toMv s) = PowerSeries.coeff n s := by
  rw [toMv, single_zero_eq_embDomain, coeff_embDomain_rename]; rfl

theorem toMv_ofMv (t : MvPowerSeries (Fin 1) R) : toMv (ofMv t) = t := by
  ext x
  obtain ⟨n, rfl⟩ : ∃ n, x = Finsupp.single 0 n := ⟨x 0, Finsupp.unique_single x⟩
  rw [coeff_toMv, ofMv, PowerSeries.coeff, coeff_killCompl, ← single_zero_eq_embDomain]

theorem toMv_injective : Function.Injective (toMv (R := R)) :=
  fun s t h => by rw [← ofMv_toMv s, ← ofMv_toMv t, h]

theorem constantCoeff_toMv (s : PowerSeries R) :
    MvPowerSeries.constantCoeff (toMv s) = PowerSeries.constantCoeff s := by
  rw [toMv, constantCoeff_rename]; rfl

theorem toMv_X : toMv (PowerSeries.X : PowerSeries R) = X 0 := by
  rw [toMv, show (PowerSeries.X : PowerSeries R) = X () from rfl, rename_X]; rfl

theorem toMv_zero : toMv (0 : PowerSeries R) = 0 := map_zero _

theorem hasSubst_toMv {s : PowerSeries R} (hs : PowerSeries.constantCoeff s = 0) :
    HasSubst (fun _ : Fin 1 => toMv s) :=
  hasSubst_of_constantCoeff_zero fun _ => by rw [constantCoeff_toMv, hs]

theorem linearPart_toMv (s : PowerSeries R) :
    linearPart (fun _ : Fin 1 => toMv s) = PowerSeries.coeff 1 s • (1 : Matrix (Fin 1) (Fin 1) R) := by
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp [linearPart, coeff_toMv]

theorem ofFormalGroup_eq_map_of_isBaseChange {S : Type*} [CommRing S] (F : FormalGroup R) (f : R →+* S)
    (G : FormalGroup S) (h : F.IsBaseChange f G) :
    ofFormalGroup G = (ofFormalGroup F).map f := by
  apply eq_of_toPowerSeries_eq
  funext i
  show rename e2 G.toPowerSeries = MvPowerSeries.map f (rename e2 F.toPowerSeries)
  unfold FormalGroup.IsBaseChange at h
  rw [h, rename_map]

theorem ofFormalGroup_map {S : Type*} [CommRing S] (F : FormalGroup R) (f : R →+* S) :
    ofFormalGroup (F.map f) = (ofFormalGroup F).map f :=
  ofFormalGroup_eq_map_of_isBaseChange F f (F.map f) rfl

omit [CommRing R] in

theorem sumElim_comp_e2 {R : Type*} [Semiring R] {τ : Type*} (a b : MvPowerSeries τ R) :
    (fun s : Fin 2 => Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) (e2 s)) = ![a, b] := by
  refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · rw [e2_zero, Sum.elim_inl, Matrix.cons_val_zero]
  · rw [e2_one, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero]

theorem nthSeries_ofFormalGroup (F : FormalGroup R) (n : ℕ) :
    (ofFormalGroup F).nthSeries n = fun _ => toMv (F.nthSeries n) := by
  induction n with
  | zero => funext i; rw [MvFormalGroup.nthSeries_zero, FormalGroup.nthSeries_zero, toMv_zero]
  | succ n ih =>
    funext i
    rw [MvFormalGroup.nthSeries_succ, ih, FormalGroup.nthSeries_succ]
    have hfam : HasSubst (Sum.elim (fun _ : Fin 1 => toMv (F.nthSeries n))
        (fun j : Fin 1 => (X j : MvPowerSeries (Fin 1) R))) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j)
      · rw [Sum.elim_inl, constantCoeff_toMv]; exact F.constantCoeff_nthSeries n
      · exact constantCoeff_X _
    show subst (Sum.elim (fun _ : Fin 1 => toMv (F.nthSeries n)) fun j => X j) (rename e2 F.toPowerSeries) =
      rename e1 (subst ![F.nthSeries n, PowerSeries.X] F.toPowerSeries)
    rw [subst_rename e2 hfam, rename_subst e1 (F.hasSubst_nthSeries n)]
    congr 1
    refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · rw [e2_zero, Sum.elim_inl, Matrix.cons_val_zero]; rfl
    · rw [e2_one, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero,
        show (PowerSeries.X : PowerSeries R) = X () from rfl, rename_X]; rfl

theorem rename_e2_lawHom_lhs (F : FormalGroup R) (s : PowerSeries R) (_hs : PowerSeries.constantCoeff s = 0) :
    rename e2 (PowerSeries.subst F.toPowerSeries s) =
      subst (ofFormalGroup F).toPowerSeries (toMv s) := by
  show rename e2 (subst (fun _ : Unit => F.toPowerSeries) s) =
    subst (fun _ : Fin 1 => rename e2 F.toPowerSeries) (rename e1 s)
  rw [rename_subst e2 (hasSubst_of_constantCoeff_zero fun _ => F.zero_constantCoeff),
    subst_rename e1 (hasSubst_of_constantCoeff_zero fun _ => by
      rw [constantCoeff_rename]; exact F.zero_constantCoeff)]

theorem rename_e2_lawHom_rhs (G : FormalGroup R) (s : PowerSeries R) (hs : PowerSeries.constantCoeff s = 0) :
    rename e2 (MvPowerSeries.subst ![FormalGroup.LawHom.substX 0 s, FormalGroup.LawHom.substX 1 s] G.toPowerSeries) =
      subst (Sum.elim
        (fun _ : Fin 1 => subst (fun l : Fin 1 => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) R)) (toMv s))
        (fun _ : Fin 1 => subst (fun l : Fin 1 => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) R)) (toMv s)))
        ((ofFormalGroup G).toPowerSeries 0) := by
  have hsX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (FormalGroup.LawHom.substX i s) = 0 := by
    intro i
    unfold FormalGroup.LawHom.substX
    exact PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) s hs
  have hL : HasSubst (![FormalGroup.LawHom.substX 0 s, FormalGroup.LawHom.substX 1 s] :
      Fin 2 → MvPowerSeries (Fin 2) R) :=
    hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨hsX 0, hsX 1⟩)
  have hcs : ∀ (b : Bool), MvPowerSeries.constantCoeff
      (subst (fun l : Fin 1 => (X (cond b (Sum.inl l) (Sum.inr l)) : MvPowerSeries (Fin 1 ⊕ Fin 1) R))
        (toMv s)) = 0 := by
    intro b
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) (by rw [constantCoeff_toMv, hs])
  have hR : HasSubst (Sum.elim
      (fun _ : Fin 1 => subst (fun l : Fin 1 => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) R)) (toMv s))
      (fun _ : Fin 1 => subst (fun l : Fin 1 => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) R)) (toMv s))) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact hcs true
    · exact hcs false
  show rename e2 (subst ![FormalGroup.LawHom.substX 0 s, FormalGroup.LawHom.substX 1 s] G.toPowerSeries) =
    subst _ (rename e2 G.toPowerSeries)
  rw [rename_subst e2 hL, subst_rename e2 hR]
  congr 1
  have key : ∀ (i : Fin 2) (c : Fin 1 → Fin 1 ⊕ Fin 1), c 0 = e2 i →
      rename e2 (FormalGroup.LawHom.substX i s) =
        subst (fun l : Fin 1 => (X (c l) : MvPowerSeries (Fin 1 ⊕ Fin 1) R)) (toMv s) := by
    intro i c hc
    unfold FormalGroup.LawHom.substX
    show rename e2 (subst (fun _ : Unit => (X i : MvPowerSeries (Fin 2) R)) s) =
      subst (fun l : Fin 1 => (X (c l) : MvPowerSeries (Fin 1 ⊕ Fin 1) R)) (rename e1 s)
    rw [rename_subst e2 (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
      subst_rename e1 (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
    congr 1
    funext u
    rw [rename_X, e1_apply, hc]
  refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · rw [e2_zero, Sum.elim_inl, Matrix.cons_val_zero]
    exact key 0 _ (e2_zero).symm
  · rw [e2_one, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact key 1 _ (e2_one).symm

theorem lawHom_comm_iff (F G : FormalGroup R) (s : PowerSeries R) (hs : PowerSeries.constantCoeff s = 0) :
    PowerSeries.subst F.toPowerSeries s =
        MvPowerSeries.subst ![FormalGroup.LawHom.substX 0 s, FormalGroup.LawHom.substX 1 s] G.toPowerSeries ↔
      ∀ i : Fin 1, subst (ofFormalGroup F).toPowerSeries (toMv s) =
        subst (Sum.elim
          (fun _ : Fin 1 => subst (fun l : Fin 1 => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) R)) (toMv s))
          (fun _ : Fin 1 => subst (fun l : Fin 1 => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) R)) (toMv s)))
          ((ofFormalGroup G).toPowerSeries i) := by
  constructor
  · intro h i
    rw [Subsingleton.elim i 0, ← rename_e2_lawHom_lhs F s hs, ← rename_e2_lawHom_rhs G s hs, h]
  · intro h
    apply rename_injective (R := R) e2
    rw [rename_e2_lawHom_lhs F s hs, rename_e2_lawHom_rhs G s hs]
    exact h 0

def _root_.FormalGroup.LawHom.toMvHom {F G : FormalGroup R} (θ : FormalGroup.LawHom F G) :
    Hom (ofFormalGroup F) (ofFormalGroup G) where
  toPowerSeries := fun _ => toMv θ.series
  constantCoeff_eq_zero := fun _ => by rw [constantCoeff_toMv]; exact θ.constantCoeff_series
  subst_eq := (lawHom_comm_iff F G θ.series θ.constantCoeff_series).mp θ.comm

@[simp] theorem _root_.FormalGroup.LawHom.toMvHom_toPowerSeries {F G : FormalGroup R}
    (θ : FormalGroup.LawHom F G) (i : Fin 1) : θ.toMvHom.toPowerSeries i = toMv θ.series := rfl

def _root_.FormalGroup.LawHom.ofMvHom {F G : FormalGroup R} (f : Hom (ofFormalGroup F) (ofFormalGroup G)) :
    FormalGroup.LawHom F G where
  series := ofMv (f.toPowerSeries 0)
  constantCoeff_series := by
    rw [← constantCoeff_toMv, toMv_ofMv]; exact f.constantCoeff_eq_zero 0
  comm := by
    have hs : PowerSeries.constantCoeff (ofMv (f.toPowerSeries 0)) = 0 := by
      rw [← constantCoeff_toMv, toMv_ofMv]; exact f.constantCoeff_eq_zero 0
    refine (lawHom_comm_iff F G _ hs).mpr fun i => ?_
    have key := f.subst_eq i
    have h0 : ∀ j : Fin 1, f.toPowerSeries j = f.toPowerSeries 0 := fun j => by
      rw [Subsingleton.elim j 0]
    simp only [h0] at key
    rw [toMv_ofMv]
    exact key

@[simp] theorem _root_.FormalGroup.LawHom.ofMvHom_series {F G : FormalGroup R}
    (f : Hom (ofFormalGroup F) (ofFormalGroup G)) : (FormalGroup.LawHom.ofMvHom f).series = ofMv (f.toPowerSeries 0) :=
  rfl

end MvFormalGroup

end



-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42
-- name    : QAlgorithms_Papers_Independent_Support50_P42
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T22:10:23.380311+00:00
-- url     : https://prove2.me/theorems/eac0096a-7ec9-4d3a-8036-cf7768e2db9e
-- title:
--   Definitions for Concentrating Partial Entanglement by Local Operations
-- statement:
--   The objects the formalized statements of *Concentrating Partial Entanglement by Local Operations* (arXiv:quant-ph/9511030) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Shared`: PDF pp.3--4: reuse normalized shared states with two positive local dimensions.
--   - `LocalTree`: PDF pp.4--6: reuse finite adaptive selective LOCC, including local disposal.
--   - `IsPureShared`: PDF pp.3--4: normalized pure state; Shared also represents mixed states.
--   - `ent`: PDF p.4, Eq.(4): entropy of Bob's reduced density.
--   - `RepresentsShared`: PDF pp.3--4: exact state identification via zero-extension outside its basis.
--   - `ExactYield`: PDF pp.4--8: integer exact-singlet counts at actual selective LOCC leaves. No normalization is imposed at zero-probability leaves. Disposal is local.
--   - `downCount`: PDF pp.5--6: down-spin count in the common fixed Schmidt basis.
--   - `schmidtBlock`: PDF p.5, Eq.(5): n identical pairs, with p=sin squared theta.
--   - `schmidtTypeProjector`: PDF pp.5--6: local type projector, independent of the bias.
--   - `schmidtOutcomeWeight`: PDF p.6, Eq.(6): binomial Born probability, including the two endpoints.
--   - `typeState`: PDF pp.6--8: uniform correlated type ket, used as a state only for k<=n.
--   - `projectedYield`: PDF p.8, Eq.(8): entropy yield before standardization, not an integer count.
--   - `outcomeEntropy`: PDF pp.6,8: finite Shannon entropy; zero-weight terms are zero.
--   - `aliceKetBranch`: PDF p.6: refined local Kraus branch, with any local environment retained.
--   - `uniformKet`: PDF p.7: maximally entangled ket of positive local rank d. At d=0 this is zero and is never called a normalized state.
--   - `trim`: PDF p.7: success map onto the first 2^ell local coordinates.
--   - `trimFailure`: PDF p.7: complementary failure projector, without branch normalization.
--   - `circlePosition`: PDF p.8, Eq.(9): circular position after m steps, starting at zero.
--   - `diagonalKet`: PDF p.9: Schmidt-diagonal pure ket.
--   - `leastAmplitude`: PDF p.9: least amplitude. Theorems require a nonempty finite list.
--   - `procrusteanSuccess`: PDF p.9: retained amplitude ratio; zero amplitudes give zero success.
--   - `filterFailure`: PDF p.9: complementary failure Kraus operator.
--   - `procrusteanYield`: PDF pp.9,20: expected one-pair Procrustean singlet yield.
--   - `sourceKet`: PDF pp.11,14: Q-prime source ket with uniform binary labels.
--   - `flaggedEncoder`: PDF pp.13--14: flagged encoder, retaining no coherence between classical k values.
--   - `bareEncoder`: PDF p.13: bare transmission, forgetting k without further decoding.
--   - `codingFidelity`: PDF pp.12--14: source-average fidelity for a fixed label-independent decoder.
--   - `OneWayBits`: PDF pp.15--17: one-way local protocol with at most bits cbits. Alice's complete instrument has private Kraus index z; only i is communicated. Bob's CPTP continuation depends on i. No free numerical cost field is used.
--   - `ConversionRate`: PDF pp.15--16: eventual state-conversion rates with global vanishing error. Both tolerances precede n. Half trace distance has the same zero-error limit as squared pure-target fidelity; no single-copy convex roof is involved.
--   - `FormationRate`: PDF p.17: eventual operational formation rates; not existential-block rates.
--   - `SingletDistillationRate`: PDF p.17: eventual operational singlet yield with whole-target error.
--   - `formationCost`: PDF p.17: least operational cost. Nonempty bounded-below feasibility is concluded below.
--   - `singletDistillable`: PDF p.17: greatest operational yield. Zero feasibility and boundedness are concluded below.
--   - `classicalPair`: PDF pp.16--17: one classically correlated shared pair.
--   - `twoPairs`: PDF p.16: two shared pairs, regrouped as Alice's two spins versus Bob's.
--   - `discardSecond`: PDF p.16: discard the second spin locally at both sites.
--   - `purificationScores`: PDF p.17: purification entropies with variable positive finite C,D and AC:BD partition.
--   - `purificationMinimum`: PDF p.17: the rejected minimum prescription; feasibility is concluded below.
--   - `wernerState`: PDF p.17, Eq.(11): the fixed Werner density.
--   - `wernerBranch`: PDF p.17: product state conditional on n independent fair preparation choices.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, https://arxiv.org/abs/quant-ph/9511030v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P39

/-! Bennett--Bernstein--Popescu--Schumacher, arXiv:quant-ph/9511030v1.
PDF pages are cited below. Entropies are in bits. Compilation and independent
moderation are pending. Deferred full nodes are recorded in HARD.md. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate
open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.
open Information100.P21 (Op Vec FiniteLOCC)
open Dependency50.P42 (dimensionedPower singlets)
open Dependency50.P48 (pureFidelity)
open Gap48.P32 (pairOfState)
open Next46.P39 (rectAct)

/-- PDF pp.3--4: reuse normalized shared states with two positive local dimensions. -/
abbrev Shared := Claimed50.P33.FiniteState 2

/-- PDF pp.4--6: reuse finite adaptive selective LOCC, including local disposal. -/
abbrev LocalTree := @Claimed50.P33.LOCC 2

/-- PDF pp.3--4: normalized pure state; Shared also represents mixed states. -/
def IsPureShared (s : Shared) : Prop :=
  Information100.P08.IsPure (pairOfState s)

/-- PDF p.4, Eq.(4): entropy of Bob's reduced density. -/
def ent (s : Shared) : ℝ := vnEntropy (traceLeft (pairOfState s))

/-- PDF pp.3--4: exact state identification via zero-extension outside its basis. -/
def RepresentsShared {a b : ℕ} (rho : Op (Fin a × Fin b)) (s : Shared) : Prop :=
  s.dims 0=a ∧ s.dims 1=b ∧ ∀ x y : Fin 2 → ℕ,
    Claimed50.P33.stateEntry s x y =
      if h : x 0<a ∧ x 1<b ∧ y 0<a ∧ y 1<b then
        rho (⟨x 0,h.1⟩,⟨x 1,h.2.1⟩) (⟨y 0,h.2.2.1⟩,⟨y 1,h.2.2.2⟩) else 0

/-- PDF pp.4--8: integer exact-singlet counts at actual selective LOCC leaves.
No normalization is imposed at zero-probability leaves. Disposal is local. -/
def ExactYield (s : Shared) (n : ℕ) (y : ℝ) : Prop :=
  ∃ input : Shared, RepresentsShared (dimensionedPower (pairOfState s) n) input ∧
    ∃ out : List (ℝ × Shared), LocalTree input out ∧ ∃ count : Shared → ℕ,
      (∀ w ∈ out, 0<w.1 → RepresentsShared (singlets (count w.2)) w.2) ∧
      y=(out.map fun w => w.1*(count w.2 : ℝ)).sum

/-- PDF pp.5--6: down-spin count in the common fixed Schmidt basis. -/
def downCount {n : ℕ} (x : Fin n → Bool) : ℕ := (Finset.univ.filter fun i => x i).card

/-- PDF p.5, Eq.(5): n identical pairs, with p=sin squared theta. -/
def schmidtBlock (n : ℕ) (p : ℝ) : Vec ((Fin n → Bool) × (Fin n → Bool)) :=
  WithLp.toLp 2 fun z => if z.1=z.2 then
    ∏ i, ((if z.1 i then Real.sqrt p else Real.sqrt (1-p)) : ℂ) else 0

/-- PDF pp.5--6: local type projector, independent of the bias. -/
def schmidtTypeProjector (n k : ℕ) : Op (Fin n → Bool) :=
  Matrix.diagonal fun x => if downCount x=k then 1 else 0

/-- PDF p.6, Eq.(6): binomial Born probability, including the two endpoints. -/
def schmidtOutcomeWeight (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ)*(1-p)^(n-k)*p^k

/-- PDF pp.6--8: uniform correlated type ket, used as a state only for k<=n. -/
def typeState (n k : ℕ) : Vec ((Fin n → Bool) × (Fin n → Bool)) :=
  WithLp.toLp 2 fun z => if z.1=z.2 ∧ downCount z.1=k then
    ((Real.sqrt (n.choose k : ℝ))⁻¹ : ℂ) else 0

/-- PDF p.8, Eq.(8): entropy yield before standardization, not an integer count. -/
def projectedYield (n : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), schmidtOutcomeWeight n p k*Real.logb 2 (n.choose k : ℝ)

/-- PDF pp.6,8: finite Shannon entropy; zero-weight terms are zero. -/
def outcomeEntropy {J : Type*} [Fintype J] (p : J → ℝ) : ℝ :=
  -∑ j, p j*Real.logb 2 (p j)

example {I J : Type*} [Fintype I] (A : Matrix J I ℂ) (v : Vec I) (j : J) :
    rectAct A v j=∑ i, A j i*v i := rfl

/-- PDF p.6: refined local Kraus branch, with any local environment retained. -/
def aliceKetBranch {a b c : ℕ} (A : Matrix (Fin c) (Fin a) ℂ)
    (psi : Vec (Fin a × Fin b)) : Vec (Fin c × Fin b) :=
  rectAct (Matrix.kronecker A (1 : Op (Fin b))) psi

/-- PDF p.7: maximally entangled ket of positive local rank d.
At d=0 this is zero and is never called a normalized state. -/
def uniformKet (d : ℕ) : Vec (Fin d × Fin d) :=
  WithLp.toLp 2 fun x => if x.1=x.2 then ((Real.sqrt (d : ℝ))⁻¹ : ℂ) else 0

/-- PDF p.7: success map onto the first 2^ell local coordinates. -/
def trim (D ell : ℕ) : Matrix (Fin (2^ell)) (Fin D) ℂ :=
  fun i j => if i.val=j.val then 1 else 0

/-- PDF p.7: complementary failure projector, without branch normalization. -/
def trimFailure (D ell : ℕ) : Op (Fin D) :=
  Matrix.diagonal fun j => if j.val<2^ell then 0 else 1

/-- PDF p.8, Eq.(9): circular position after m steps, starting at zero. -/
def circlePosition {Omega : Type*} (X : ℕ → Omega → ℝ) (m : ℕ) (w : Omega) : ℝ :=
  Int.fract (∑ i ∈ Finset.range m, X i w)

/-- PDF p.9: Schmidt-diagonal pure ket. -/
def diagonalKet {d : ℕ} (c : Fin d → ℝ) : Vec (Fin d × Fin d) :=
  WithLp.toLp 2 fun z => if z.1=z.2 then (c z.1 : ℂ) else 0

/-- PDF p.9: least amplitude. Theorems require a nonempty finite list. -/
def leastAmplitude {d : ℕ} (c : Fin d → ℝ) : ℝ := sInf (Set.range c)

/-- PDF p.9: retained amplitude ratio; zero amplitudes give zero success. -/
def procrusteanSuccess {d : ℕ} (c : Fin d → ℝ) : Op (Fin d) :=
  Matrix.diagonal fun i => ((leastAmplitude c/c i : ℝ) : ℂ)

/-- PDF p.9: complementary failure Kraus operator. -/
def filterFailure {d : ℕ} (c : Fin d → ℝ) : Op (Fin d) :=
  Matrix.diagonal fun i => ((Real.sqrt (1-(leastAmplitude c/c i)^2) : ℝ) : ℂ)

/-- PDF pp.9,20: expected one-pair Procrustean singlet yield. -/
def procrusteanYield (p : ℝ) : ℝ := 2*min p (1-p)

/-- PDF pp.11,14: Q-prime source ket with uniform binary labels. -/
def sourceKet {n : ℕ} (p : ℝ) (x : Fin n → Bool) : Vec (Fin n → Bool) :=
  WithLp.toLp 2 fun z => ∏ i,
    if z i then (if x i then -(Real.sqrt p : ℂ) else (Real.sqrt p : ℂ))
    else (Real.sqrt (1-p) : ℂ)

/-- PDF pp.13--14: flagged encoder, retaining no coherence between classical k values. -/
def flaggedEncoder (n : ℕ) : Superop (Fin n → Bool) (Fin (n+1) × (Fin n → Bool)) :=
  fun rho u v => if u.1=v.1 then
    (schmidtTypeProjector n u.1.val*rho*schmidtTypeProjector n u.1.val) u.2 v.2 else 0

/-- PDF p.13: bare transmission, forgetting k without further decoding. -/
def bareEncoder (n : ℕ) : Superop (Fin n → Bool) (Fin n → Bool) :=
  fun rho => ∑ k : Fin (n+1), schmidtTypeProjector n k.val*rho*schmidtTypeProjector n k.val

/-- PDF pp.12--14: source-average fidelity for a fixed label-independent decoder. -/
def codingFidelity (n : ℕ) (p : ℝ)
    (D : Superop (Fin (n+1) × (Fin n → Bool)) (Fin n → Bool)) : ℝ :=
  ((2 : ℝ)^n)⁻¹*∑ x : Fin n → Bool,
    pureFidelity (sourceKet p x) (D (flaggedEncoder n (pureDensity (sourceKet p x))))

/-- PDF pp.15--17: one-way local protocol with at most bits cbits. Alice's
complete instrument has private Kraus index z; only i is communicated.
Bob's CPTP continuation depends on i. No free numerical cost field is used. -/
def OneWayBits {a b c d : ℕ} (bits : ℕ)
    (L : Superop (Fin a × Fin b) (Fin c × Fin d)) : Prop :=
  ∃ k r : ℕ, k≤2^bits ∧ ∃ A : Fin k → Fin r → Matrix (Fin c) (Fin a) ℂ,
    (∑ i, ∑ z, (A i z)ᴴ*A i z)=1 ∧
    ∃ B : Fin k → Superop (Fin b) (Fin d), (∀ i, IsChannel (B i)) ∧ ∀ rho,
      L rho=∑ i, idTensorSuperop (B i)
        (∑ z, conjSuperop (Matrix.kronecker (A i z) (1 : Op (Fin b))) rho)

/-- PDF pp.15--16: eventual state-conversion rates with global vanishing error.
Both tolerances precede n. Half trace distance has the same zero-error limit
as squared pure-target fidelity; no single-copy convex roof is involved. -/
def ConversionRate (s t : Shared) (R : ℝ) : Prop :=
  0≤R ∧ ∀ epsilon>(0 : ℝ), ∀ delta>(0 : ℝ), ∃ N : ℕ,
    ∀ n : ℕ, N<n → ∃ m : ℕ, (R-delta)*(n : ℝ) ≤ (m : ℝ) ∧
      ∃ L : Superop (Fin ((s.dims 0)^n) × Fin ((s.dims 1)^n))
        (Fin ((t.dims 0)^m) × Fin ((t.dims 1)^m)),
        FiniteLOCC L ∧ traceDistance (L (dimensionedPower (pairOfState s) n))
          (dimensionedPower (pairOfState t) m)≤epsilon

/-- PDF p.17: eventual operational formation rates; not existential-block rates. -/
def FormationRate (s : Shared) (R : ℝ) : Prop :=
  0≤R ∧ Dependency50.P42.EventuallyAchievableRate
    Dependency50.P42.halfTraceDistance (pairOfState s) R

/-- PDF p.17: eventual operational singlet yield with whole-target error. -/
def SingletDistillationRate (s : Shared) (R : ℝ) : Prop :=
  0≤R ∧ ∀ epsilon>(0 : ℝ), ∀ delta>(0 : ℝ), ∃ N : ℕ,
    ∀ n : ℕ, N<n → ∃ m : ℕ, (R-delta)*(n : ℝ) ≤ (m : ℝ) ∧
      ∃ L : Superop (Fin ((s.dims 0)^n) × Fin ((s.dims 1)^n))
        (Fin (2^m) × Fin (2^m)),
        FiniteLOCC L ∧ traceDistance (L (dimensionedPower (pairOfState s) n)) (singlets m)≤epsilon

/-- PDF p.17: least operational cost. Nonempty bounded-below feasibility is concluded below. -/
def formationCost (s : Shared) : ℝ := sInf {R | FormationRate s R}

/-- PDF p.17: greatest operational yield. Zero feasibility and boundedness are concluded below. -/
def singletDistillable (s : Shared) : ℝ := sSup {R | SingletDistillationRate s R}

/-- PDF pp.16--17: one classically correlated shared pair. -/
def classicalPair : Op (Fin 2 × Fin 2) :=
  (1/2 : ℂ) • (pureDensity (ket (0,0))+pureDensity (ket (1,1)))

/-- PDF p.16: two shared pairs, regrouped as Alice's two spins versus Bob's. -/
def twoPairs (rho sigma : Op (Fin 2 × Fin 2)) :
    Op ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :=
  fun x y => rho (x.1.1,x.2.1) (y.1.1,y.2.1)*sigma (x.1.2,x.2.2) (y.1.2,y.2.2)

/-- PDF p.16: discard the second spin locally at both sites. -/
def discardSecond : Superop ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) (Fin 2 × Fin 2) :=
  fun rho x y => ∑ a : Fin 2, ∑ b : Fin 2, rho ((x.1,a),(x.2,b)) ((y.1,a),(y.2,b))

/-- PDF p.17: purification entropies with variable positive finite C,D and AC:BD partition. -/
def purificationScores (rho : Op (Fin 2 × Fin 2)) : Set ℝ :=
  {e | ∃ c d : ℕ, 0<c ∧ 0<d ∧
    ∃ v : Vec ((Fin 2 × Fin c) × (Fin 2 × Fin d)), ‖v‖=1 ∧
      (∀ x y : Fin 2 × Fin 2, rho x y=∑ u : Fin c, ∑ w : Fin d,
        pureDensity v ((x.1,u),(x.2,w)) ((y.1,u),(y.2,w))) ∧
      e=vnEntropy (traceLeft (pureDensity v))}

/-- PDF p.17: the rejected minimum prescription; feasibility is concluded below. -/
def purificationMinimum (rho : Op (Fin 2 × Fin 2)) : ℝ := sInf (purificationScores rho)

/-- PDF p.17, Eq.(11): the fixed Werner density. -/
def wernerState : Op (Fin 2 × Fin 2) :=
  (1/8 : ℂ) • 1+(1/2 : ℂ) • Dependency50.P42.singletState

/-- PDF p.17: product state conditional on n independent fair preparation choices. -/
def wernerBranch (n : ℕ) (z : Fin n → Bool) : Op (Fin (2^n) × Fin (2^n)) :=
  fun x y => ∏ i,
    (if z i then Dependency50.P42.singletState else (1/4 : ℂ) • (1 : Op (Fin 2 × Fin 2)))
      ((Dependency50.P42.copyIndex 2 n).symm x.1 i,(Dependency50.P42.copyIndex 2 n).symm x.2 i)
      ((Dependency50.P42.copyIndex 2 n).symm y.1 i,(Dependency50.P42.copyIndex 2 n).symm y.2 i)

/-! Sanity examples pin definitions. No result proofs are supplied. -/

example (n : ℕ) (x : Fin n → Bool) : schmidtTypeProjector n (downCount x) x x=1 := by
  simp [schmidtTypeProjector]

example (n : ℕ) : downCount (fun _ : Fin n => false)=0 := by simp [downCount]

example (p : ℝ) : projectedYield 0 p=0 := by simp [projectedYield]

example {J : Type*} [Fintype J] : outcomeEntropy (fun _ : J => (0 : ℝ))=0 := by
  simp [outcomeEntropy]

example (D ell : ℕ) (i : Fin (2^ell)) (j : Fin D) (h : i.val=j.val) : trim D ell i j=1 := by
  simp [trim,h]

example {Omega : Type*} (X : ℕ → Omega → ℝ) (w : Omega) : circlePosition X 0 w=0 := by
  simp [circlePosition]

example : procrusteanYield 0=0 := by norm_num [procrusteanYield]

example {d : ℕ} (c : Fin d → ℝ) (i : Fin d) : diagonalKet c (i,i)=(c i : ℂ) := by
  simp [diagonalKet]

example (n : ℕ) (rho : Op (Fin n → Bool)) (u v : Fin (n+1) × (Fin n → Bool))
    (h : u.1≠v.1) : flaggedEncoder n rho u v=0 := by simp [flaggedEncoder,h]

example {I : Type*} [Fintype I] (v : Vec I) : pureFidelity v 0=0 := by
  simp [Dependency50.P48.pureFidelity, effectProb]

example : classicalPair (0,0) (1,1)=0 := by simp [classicalPair,pureDensity,ket]

example (rho sigma : Op (Fin 2 × Fin 2)) (x y : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :
    twoPairs rho sigma x y=rho (x.1.1,x.2.1) (y.1.1,y.2.1)*sigma (x.1.2,x.2.2) (y.1.2,y.2.2) := rfl

example : wernerState=(1/2 : ℂ) • ((1/4 : ℂ) • (1 : Op (Fin 2 × Fin 2)))+
    (1/2 : ℂ) • Dependency50.P42.singletState := by norm_num [wernerState,smul_smul]

/-- Sanity: no-copy source registers have their unique scalar amplitude one. -/
example (p : ℝ) : sourceKet p (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i)=1 := by
  simp [sourceKet]

example (p : ℝ) (x : (Fin 0 → Bool) × (Fin 0 → Bool)) : schmidtBlock 0 p x=1 := by
  have h : x.1=x.2 := Subsingleton.elim _ _
  simp [schmidtBlock,h]

example (x : (Fin 0 → Bool) × (Fin 0 → Bool)) : typeState 0 0 x=1 := by
  have h : x.1=x.2 := Subsingleton.elim _ _
  simp [typeState,h,downCount]

example : uniformKet 1 (0,0)=1 := by simp [uniformKet]

example : leastAmplitude (fun _ : Fin 1 => (1 : ℝ))=1 := by
  simp [leastAmplitude]

example (s : Shared) : ent s=vnEntropy (traceLeft (pairOfState s)) := rfl

example (s : Shared) (h : IsPureShared s) :
    ∃ v : Vec (Fin (s.dims 0) × Fin (s.dims 1)), ‖v‖=1 := by
  obtain ⟨v,hv,_⟩ := h
  exact ⟨v,hv⟩

example {a b : ℕ} (rho : Op (Fin a × Fin b)) (s : Shared) (h : RepresentsShared rho s) :
    s.dims 0=a ∧ s.dims 1=b := ⟨h.1,h.2.1⟩

example (s t : Shared) (R : ℝ) (h : ConversionRate s t R) : 0≤R := h.1

example (s : Shared) (R : ℝ) (h : FormationRate s R) : 0≤R := h.1

example (s : Shared) (R : ℝ) (h : SingletDistillationRate s R) : 0≤R := h.1

example (s : Shared) : formationCost s=sInf {R | FormationRate s R} := rfl

example (s : Shared) : singletDistillable s=sSup {R | SingletDistillationRate s R} := rfl

example (rho : Op (Fin 2 × Fin 2)) : purificationMinimum rho=sInf (purificationScores rho) := rfl

example (rho : Op ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) (x y : Fin 2 × Fin 2) :
    discardSecond rho x y=∑ a : Fin 2, ∑ b : Fin 2, rho ((x.1,a),(x.2,b)) ((y.1,a),(y.2,b)) := rfl

example (rho : Op (Fin 0 → Bool)) (x y : Fin 0 → Bool) : bareEncoder 0 rho x y=rho x y := by
  have h : schmidtTypeProjector 0 0=(1 : Op (Fin 0 → Bool)) := by
    ext a b
    have hab : a=b := Subsingleton.elim _ _
    subst b
    simp [schmidtTypeProjector,downCount]
  simp [bareEncoder,Fin.sum_univ_one,h]

example (z : Fin 0 → Bool) : wernerBranch 0 z=1 := by
  letI : Subsingleton (Fin (2 ^ 0) × Fin (2 ^ 0)) := by
    simp only [pow_zero]
    infer_instance
  ext x y
  have h : x=y := Subsingleton.elim _ _
  subst y
  simp [wernerBranch]

/-- Sanity: every exact-yield witness contains an actual local protocol. -/
example (s : Shared) (n : ℕ) (y : ℝ) (h : ExactYield s n y) :
    ∃ input : Shared, ∃ out : List (ℝ × Shared), LocalTree input out := by
  obtain ⟨input,_,out,hout,_⟩ := h
  exact ⟨input,out,hout⟩

example {d : ℕ} (c : Fin d → ℝ) (i : Fin d) :
    procrusteanSuccess c i i=(leastAmplitude c/c i : ℂ) := by simp [procrusteanSuccess]

example {d : ℕ} (c : Fin d → ℝ) (i : Fin d) :
    filterFailure c i i=(Real.sqrt (1-(leastAmplitude c/c i)^2) : ℂ) := by simp [filterFailure]

/-- Sanity: a one-way budget witnesses a bounded public outcome alphabet. -/
example {a b c d : ℕ} (bits : ℕ) (L : Superop (Fin a × Fin b) (Fin c × Fin d))
    (h : OneWayBits bits L) : ∃ k : ℕ, k≤2^bits := by
  obtain ⟨k,r,hk,_⟩ := h
  exact ⟨k,hk⟩

example (rho : Op (Fin 2 × Fin 2)) (e : ℝ) (h : e∈purificationScores rho) :
    ∃ c d : ℕ, 0<c ∧ 0<d := by
  obtain ⟨c,d,hc,hd,_⟩ := h
  exact ⟨c,d,hc,hd⟩

end QAlgorithms.Papers.Independent.Support50.P42



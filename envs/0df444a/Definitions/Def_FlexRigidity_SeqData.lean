-- Prove2me | Definitions.Def_FlexRigidity_SeqData
-- name    : FlexRigidity_SeqData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:16:39.710325+00:00
-- url     : https://prove2.me/theorems/b6530262-730d-4912-a3aa-6b1cd65de4c0
-- title:
--   Sequential channel pairs, Postulate Set 4.1(i)
-- statement:
--   The data of Postulate Set 4.1(i): for every round $i$, a channel $\mathcal G_i\in\mathrm{CPTP}(M_i,Z_iS_iJ_i)$ whose output $Z_i$ is classical and determines the record $C_i\in C$; a controlled replacer $\mathcal P_i$ of the form (16) with registers $Z_iS_iJ_i$ (control $Z_i$), $a_z=1$ and normalized positive definite replacement states $\omega^z_{S_i}$, $z\notin\mathcal Z_i^*$; and a channel $\mathcal T_i\in\mathrm{CPTP}(Z_iS_iJ_i,C_iO_iM_{i+1})$ that only uses $C_i$ as a control register. The real and ideal round channels are
--   $$\mathcal E_i=\mathcal T_i\circ\mathcal G_i,\qquad\mathcal F_i=\mathcal T_i\circ\mathcal P_i\circ\mathcal G_i.$$
--   `IsPostulate41 n` states these conditions for the first $n$ rounds.
--
--   **Formalization Note** "$\mathcal T_i$ only uses $C_i$ as a control register" is formalized as: every operator supported on the block $C_i=c$ is mapped to an operator supported on the output block $C_i=c$ — the property the paper uses ("Since $\mathcal T_i$ preserves $C_i$", p. 29). Families are indexed by all rounds $i\in\mathbb N$; only the first $n$ enter a statement.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Postulate Set 4.1(i), p. 28; p. 29

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_ctrlReplacer
import Definitions.Def_FlexRigidity_HasClassicalFirst
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Sequential channel pairs, Postulate Set 4.1(i)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 28). Round `k` has
`G_k ∈ CPTP(M_k, Z_k S_k J_k)` with classical output `Z_k`, the record `C_k` being a function
`cOf k : Z_k → C` of `Z_k`; a controlled replacer `P_k` of the form (16) with registers
`Z_k S_k J_k` (control `Z_k`), `a_z = 1` and normalized positive definite replacement states
`ω k z` for `z ∉ Zs k`; and `T_k ∈ CPTP(Z_k S_k J_k, C_k O_k M_{k+1})` that only uses `C_k` as a
control register. Then `E_k = T_k ∘ G_k` and `F_k = T_k ∘ P_k ∘ G_k`. -/
structure SeqData (C : Type) (O M Z S J : ℕ → Type) where
  /-- the record `C_k` as a function of the classical output `Z_k` ("`Z_k` includes `C_k`") -/
  cOf : (k : ℕ) → Z k → C
  /-- `G_k ∈ CPTP(M_k, Z_k S_k J_k)` -/
  G : (k : ℕ) → Superop (M k) (Z k × S k × J k)
  /-- the set `Z*` of control values left untouched by `P_k` -/
  Zs : (k : ℕ) → Finset (Z k)
  /-- the replacement states `ω^z_{S_k}`, used for `z ∉ Z*` -/
  ω : (k : ℕ) → Z k → Matrix (S k) (S k) ℂ
  /-- `T_k ∈ CPTP(Z_k S_k J_k, C_k O_k M_{k+1})` -/
  T : (k : ℕ) → Superop (Z k × S k × J k) ((C × O k) × M (k + 1))

namespace SeqData

variable {C : Type} {O M Z S J : ℕ → Type}

/-- The controlled replacer `P_k` of the form (16) with `a_z = 1`. -/
def P [∀ k, DecidableEq (Z k)] [∀ k, Fintype (S k)] (D : SeqData C O M Z S J) (k : ℕ) :
    Superop (Z k × S k × J k) (Z k × S k × J k) :=
  ctrlReplacer (D.Zs k) (fun _ => 1) (D.ω k)

/-- The real round channel `E_k = T_k ∘ G_k`. -/
def E (D : SeqData C O M Z S J) (k : ℕ) : Superop (M k) ((C × O k) × M (k + 1)) :=
  fun X => D.T k (D.G k X)

/-- The ideal round channel `F_k = T_k ∘ P_k ∘ G_k`. -/
def F [∀ k, DecidableEq (Z k)] [∀ k, Fintype (S k)] (D : SeqData C O M Z S J) (k : ℕ) :
    Superop (M k) ((C × O k) × M (k + 1)) :=
  fun X => D.T k (D.P k (D.G k X))

/-- **Postulate Set 4.1(i)** for rounds `k < n`: `G_k` and `T_k` are channels, `G_k` has classical
output `Z_k`, the replacement states for `z ∉ Z*` are normalized and positive definite, and `T_k`
only uses `C_k` as a control register: every operator supported on the block `C_k = c` (both
indices in that block) is mapped to an operator supported on the output block `C_k = c`. -/
def IsPostulate41 [Fintype C] [∀ k, Fintype (O k)] [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)] [∀ k, Fintype (Z k)]
    [∀ k, DecidableEq (Z k)] [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)]
    [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)] (D : SeqData C O M Z S J) (n : ℕ) : Prop :=
  ∀ k < n,
    IsChannel (D.G k) ∧ HasClassicalFirst (D.G k) ∧
    (∀ z ∉ D.Zs k, (D.ω k z).PosDef ∧ tr (D.ω k z) = 1) ∧
    IsChannel (D.T k) ∧
    (∀ (c : C) (X : Matrix (Z k × S k × J k) (Z k × S k × J k) ℂ),
      (∀ i j, X i j ≠ 0 → D.cOf k i.1 = c ∧ D.cOf k j.1 = c) →
      ∀ i j, D.T k X i j ≠ 0 → i.1.1 = c ∧ j.1.1 = c)

end SeqData

end FlexRigidity



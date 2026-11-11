-- Prove2me | Definitions.Def_FlexRigidity_StoredImpl
-- name    : FlexRigidity_StoredImpl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:19:04.781159+00:00
-- url     : https://prove2.me/theorems/b8c20768-1d4d-4126-91fa-36a53e63dbf9
-- title:
--   Devices in stored-output form, eq. (47)
-- statement:
--   In round $i$ Alice's device appends an ancilla $M'^{\mathrm A}_i$ in $|0\rangle$, measures projectors $\{H^x_{i,a}\}_a$ on $M^{\mathrm A}_iM'^{\mathrm A}_i$, keeps $a$, and applies a channel $L^{\mathrm A,x,a}_i$ to $M^{\mathrm A}_{i+1}$; Bob's test operation uses $M'^{\mathrm B}_i$, projectors $\{K^y_{i,b}\}_b$ and channels $L^{\mathrm B,y,b}_i$; his generation operation is a channel $\mathcal E^{\mathrm B,\mathrm{gen}}_i$. So $\mathcal E^{\mathrm A,x,a}_i[\rho]=L^{\mathrm A,x,a}_i[H^x_{i,a}(\rho\otimes|0\rangle\langle0|)H^x_{i,a}]$.
--
--   **Formalization Note** The ancilla has dimension $k+1$ with $|0\rangle$ its first basis vector.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (47), p. 44

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_IsProjMeas
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Devices in stored-output form, eq. (47)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 44): in round `i`, Alice's device appends an
ancilla `M′^A_i` in the state `|0⟩`, measures the projectors `{H^x_{i,a}}_a` on `M^A_i M′^A_i`, keeps
`a`, and applies a channel `L^{A,x,a}_i ∈ CPTP(M^A_i M′^A_i, M^A_{i+1})`; Bob's test operation
likewise uses `M′^B_i`, projectors `{K^y_{i,b}}_b` and channels `L^{B,y,b}_i`; Bob's generation
operation is a channel `E^{B,gen}_i : M^B_i → M^B_{i+1}`.

`IsValid n` says that for rounds `i < n` the families are projective and the maps are channels.

**Formalization Note** The ancilla `M′^A_i` is `Fin (kA i + 1)` with `|0⟩` the basis vector `0`
(every finite ancilla with a fixed `|0⟩` is of this form up to relabelling). -/
structure StoredImpl (X Y A B : Type) where
  /-- dimension of `M^A_i` -/
  dA : ℕ → ℕ
  /-- dimension of `M^B_i` -/
  dB : ℕ → ℕ
  /-- `M′^A_i = Fin (kA i + 1)` -/
  kA : ℕ → ℕ
  /-- `M′^B_i = Fin (kB i + 1)` -/
  kB : ℕ → ℕ
  /-- Alice's projectors `H^x_{i,a}` on `M^A_i M′^A_i` -/
  H : (i : ℕ) → X → A → Matrix (Fin (dA i) × Fin (kA i + 1)) (Fin (dA i) × Fin (kA i + 1)) ℂ
  /-- Bob's projectors `K^y_{i,b}` on `M^B_i M′^B_i` -/
  K : (i : ℕ) → Y → B → Matrix (Fin (dB i) × Fin (kB i + 1)) (Fin (dB i) × Fin (kB i + 1)) ℂ
  /-- Alice's continuations `L^{A,x,a}_i` -/
  LA : (i : ℕ) → X → A → Superop (Fin (dA i) × Fin (kA i + 1)) (Fin (dA (i + 1)))
  /-- Bob's test continuations `L^{B,y,b}_i` -/
  LB : (i : ℕ) → Y → B → Superop (Fin (dB i) × Fin (kB i + 1)) (Fin (dB (i + 1)))
  /-- Bob's generation channel `E^{B,gen}_i` -/
  EBg : (i : ℕ) → Superop (Fin (dB i)) (Fin (dB (i + 1)))

/-- The stored-output data are valid for rounds `i < n`. -/
def StoredImpl.IsValid {X Y A B : Type} [Fintype A] [Fintype B] (I : StoredImpl X Y A B)
    (n : ℕ) : Prop :=
  ∀ i < n, (∀ x, IsProjMeas (I.H i x)) ∧ (∀ y, IsProjMeas (I.K i y)) ∧
    (∀ x a, IsChannel (I.LA i x a)) ∧ (∀ y b, IsChannel (I.LB i y b)) ∧ IsChannel (I.EBg i)

/-- Alice's instrument element `E^{A,x,a}_i[ρ] = L^{A,x,a}_i[H^x_{i,a}(ρ ⊗ |0⟩⟨0|)H^x_{i,a}]`. -/
def StoredImpl.instA {X Y A B : Type} (I : StoredImpl X Y A B) (i : ℕ) (x : X) (a : A) :
    Superop (Fin (I.dA i)) (Fin (I.dA (i + 1))) :=
  fun ρ => I.LA i x a (I.H i x a * Matrix.kronecker ρ (Matrix.single 0 0 1) * I.H i x a)

/-- Bob's test instrument element `E^{B,test,y,b}_i[ρ] = L^{B,y,b}_i[K^y_{i,b}(ρ ⊗ |0⟩⟨0|)K^y_{i,b}]`. -/
def StoredImpl.instB {X Y A B : Type} (I : StoredImpl X Y A B) (i : ℕ) (y : Y) (b : B) :
    Superop (Fin (I.dB i)) (Fin (I.dB (i + 1))) :=
  fun ρ => I.LB i y b (I.K i y b * Matrix.kronecker ρ (Matrix.single 0 0 1) * I.K i y b)

end FlexRigidity



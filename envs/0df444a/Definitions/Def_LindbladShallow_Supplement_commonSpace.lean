-- Prove2me | Definitions.Def_LindbladShallow_Supplement_commonSpace
-- name    : LindbladShallow_Supplement_commonSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:21:15.159815+00:00
-- url     : https://prove2.me/theorems/34a88233-369f-477c-9b5e-dbbc8c7eda58
-- title:
--   The factor's hardware, physical and common spaces, the inclusions $J_{P,C}$, $J_{H,C}$, the extension $U^c$ and $I_P$ (§5.2)
-- statement:
--   Fix a factor $W_C$ (a valid input, $M$, $R$, an owner cube $C$), a record capacity $C_{\mathrm{cap}}$ and a number $n_W$ of signal and work qubits.
--
--   1. The **hardware space** consists of all system qubits, the bits of the list registers of the complete owner blocks, $n_W$ signal and work qubits, and the physical baths outside the complete local bath set $B_{\mathrm{cat}}$ (untouched by the factor).
--   2. The **physical space** is system $\otimes$ all physical baths $\otimes$ the $n_W$ work qubits.
--   3. The **common space** is system $\otimes$ work qubits $\otimes\bigotimes_A K_A\otimes$ the outside baths. The inclusions $J_{P,C}=I\otimes\bigotimes_A j_{P,A}$ and $J_{H,C}=I\otimes\bigotimes_A j_{H,A}$ embed the physical and the hardware space.
--   4. For a hardware or physical unitary $U$ the **unitary extension** is
--   $$
--   U^c=J\,U\,J^\dagger+I-JJ^\dagger,
--   $$
--   with $J=J_{H,C}$ or $J=J_{P,C}$ respectively (Eq. (41)).
--   5. $I_P=J_{P,C}E_{\mathrm{init}}$ places physical data into zero signal and work registers and then into the common space, keeping every physical bath configuration, including those above capacity.
--   6. A **logical circuit** is a list of exact one-qubit unitaries and CNOTs on the logical qubits: a chosen set of system qubits, the environment bits and the signal and work qubits. Its unitary extends to the hardware space by the identity on the other system qubits and the outside baths. On a host of grid positions an injective placement of the logical qubits turns it into a host unitary, the identity on unoccupied positions.
--
--   These maps state the error of Theorem 5.1 on the whole initialized output, including amplitude outside the signal subspace and physical occupations above the record capacity.
--
--   **Formalization Note** The other owners' signal and work registers, initialized to zero by $I_P$ and untouched by the factor, are left out of the common space; this changes no norm. Each inclusion is the 0/1 matrix of an injective map of basis states.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), §5.2, Eq. (41), p.42; Table 5, p.43; Table 4, p.38; Eq. (35), p.37

import Mathlib
import Definitions.Def_LindbladShallow_Supplement_listEnc
import Definitions.Def_LindbladShallow_routing

open scoped Matrix ComplexOrder

namespace LindbladShallow

namespace Supplement

variable {P : Params}

/-- The physical bath labels outside the complete local bath set `B_cat` of factor `C`; the factor
acts as the identity on them. -/
abbrev Outside (I : Instance P) (M R : ℕ) (C : Fin P.D → ℤ) := {b : BJ I M // b ∉ Bcat I M R C}

noncomputable instance (I : Instance P) (M R : ℕ) (C : Fin P.D → ℤ) :
    Fintype (Outside I M R C) := by
  classical
  infer_instance

/-- The environment bits of the factor's hardware (Table 4, p.38): for each complete owner block
`A`, each record `ℓ < C_cap`, its label bits and its value bits. -/
abbrev EnvBit (I : Instance P) (M R : ℕ) (C : Fin P.D → ℤ) (Ccap : ℕ) :=
  Σ A : {A // A ∈ blocksOf I R C}, Fin Ccap × (Fin (wlab I M R A.1) ⊕ Fin (wval P))

/-- The hardware qubits of the factor: every system qubit, the environment bits, and `nW` signal and
work qubits (Table 4, p.38). -/
abbrev HwWire (I : Instance P) (M R : ℕ) (C : Fin P.D → ℤ) (Ccap nW : ℕ) :=
  (Fin I.n × Fin P.d0) ⊕ (EnvBit I M R C Ccap ⊕ Fin nW)

/-- The hardware space: a value of every hardware qubit, together with the physical baths outside
`B_cat` (untouched by the factor). -/
abbrev HwSp (I : Instance P) (M R : ℕ) (C : Fin P.D → ℤ) (Ccap nW : ℕ) :=
  (HwWire I M R C Ccap nW → Bool) × (Outside I M R C → Fin (dEm1 P + 1))

/-- The physical space with the factor's signal and work registers: system ⊗ all physical baths
⊗ `nW` work qubits. -/
abbrev PhysSp (I : Instance P) (M nW : ℕ) := Tot I M × (Fin nW → Bool)

/-- The common comparison space of the factor (§5.2, p.42): the system, the signal and work
registers, `K_A` for every complete owner block `A`, and the physical baths outside `B_cat`. -/
abbrev CommSp (I : Instance P) (M R : ℕ) (C : Fin P.D → ℤ) (Ccap nW : ℕ) :=
  Sys I × (Fin nW → Bool) × ((A : {A // A ∈ blocksOf I R C}) → KBlock I M R A.1 Ccap) ×
    (Outside I M R C → Fin (dEm1 P + 1))

/-- The 0/1 matrix `|f(b)⟩⟨b|` of a map of basis states. -/
noncomputable def fnMat {α β : Type*} [DecidableEq α] (f : β → α) : Matrix α β ℂ :=
  Matrix.of fun a b => if a = f b then 1 else 0

/-- The physical inclusion on basis states: block baths go to `j_{P,A} = Sum.inl`, outside baths and
the system and work values are kept. -/
def physToComm (I : Instance P) (M R : ℕ) (C : Fin P.D → ℤ) (Ccap nW : ℕ)
    (p : PhysSp I M nW) : CommSp I M R C Ccap nW :=
  (p.1.1, p.2, fun _ => Sum.inl fun b => p.1.2 b.1, fun o => p.1.2 o.1)

/-- The list register of block `A` read off the hardware qubits. -/
def blockOfHw (I : Instance P) (M R : ℕ) (C : Fin P.D → ℤ) (Ccap nW : ℕ)
    (ω : HwWire I M R C Ccap nW → Bool) (A : {A // A ∈ blocksOf I R C}) :
    HwBlock I M R A.1 Ccap :=
  fun ℓ => (fun i => ω (Sum.inr (Sum.inl ⟨A, ℓ, Sum.inl i⟩)),
    fun i => ω (Sum.inr (Sum.inl ⟨A, ℓ, Sum.inr i⟩)))

/-- The hardware inclusion on basis states: each block's list register goes through `j_{H,A}`. -/
noncomputable def hwToComm (I : Instance P) (M R : ℕ) (C : Fin P.D → ℤ) (Ccap nW : ℕ)
    (q : HwSp I M R C Ccap nW) : CommSp I M R C Ccap nW :=
  (fun x => q.1 (Sum.inl x), fun i => q.1 (Sum.inr (Sum.inr i)),
    fun A => jH I M R A.1 (blockOfHw I M R C Ccap nW q.1 A), q.2)

/-- `J_{P,C}`: the physical inclusion `I_{X_C} ⊗ ⨂_A j_{P,A}` (§5.2, p.42), with the identity on the
outside baths. -/
noncomputable def JP (I : Instance P) (M R : ℕ) (C : Fin P.D → ℤ) (Ccap nW : ℕ) :
    Matrix (CommSp I M R C Ccap nW) (PhysSp I M nW) ℂ :=
  open Classical in fnMat (physToComm I M R C Ccap nW)

/-- `J_{H,C}`: the hardware inclusion `I_{X_C} ⊗ ⨂_A j_{H,A}` (§5.2, p.42), with the identity on the
outside baths. -/
noncomputable def JH (I : Instance P) (M R : ℕ) (C : Fin P.D → ℤ) (Ccap nW : ℕ) :
    Matrix (CommSp I M R C Ccap nW) (HwSp I M R C Ccap nW) ℂ :=
  open Classical in fnMat (hwToComm I M R C Ccap nW)

/-- The unitary extension `U^c = J U J† + I − J J†` (Eq. (41), p.42). -/
noncomputable def unitaryExt {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (J : Matrix α β ℂ) (U : Matrix β β ℂ) : Matrix α α ℂ :=
  J * U * Jᴴ + (1 - J * Jᴴ)

/-- `I_P = J^all_P E_init` on the factor (Table 5, p.43): physical data `Tot` placed into zero signal
and work registers, then into the common space. -/
noncomputable def IP (I : Instance P) (M R : ℕ) (C : Fin P.D → ℤ) (Ccap nW : ℕ) :
    Matrix (CommSp I M R C Ccap nW) (Tot I M) ℂ :=
  JP I M R C Ccap nW * (Matrix.of fun (p : PhysSp I M nW) (t : Tot I M) =>
    if p = (t, fun _ => false) then (1 : ℂ) else 0)

/-- A physical operator on `Tot` tensored with the identity on the work qubits. -/
def liftPhys {I : Instance P} {M nW : ℕ} (W : Matrix (Tot I M) (Tot I M) ℂ) :
    Matrix (PhysSp I M nW) (PhysSp I M nW) ℂ :=
  Matrix.of fun p q => if p.2 = q.2 then W p.1 q.1 else 0

/-- The logical qubits of a construction: the chosen system qubits `sysW`, the environment bits and
the `nW` signal and work qubits (Theorem 5.1: "its system, complete owner environment blocks,
signal and work registers"). -/
abbrev LW (I : Instance P) (M R : ℕ) (C : Fin P.D → ℤ) (Ccap nW : ℕ)
    (sysW : Finset (Fin I.n × Fin P.d0)) :=
  {q // q ∈ sysW} ⊕ (EnvBit I M R C Ccap ⊕ Fin nW)

/-- A logical gate: an exact one-qubit unitary on a wire, or a CNOT `CX` (control, target). -/
inductive LGate (W : Type)
  | one (U : Matrix (Fin 2) (Fin 2) ℂ) (w : W)
  | cx (a b : W)

/-- A legal logical gate: the one-qubit matrix is unitary; a CNOT has distinct control and target. -/
def LGate.Legal {W : Type} : LGate W → Prop
  | .one U _ => U ∈ Matrix.unitaryGroup (Fin 2) ℂ
  | .cx a b => a ≠ b

/-- The unitary of a logical gate on the register `W → Bool`. -/
noncomputable def LGate.mat {W : Type} [DecidableEq W] : LGate W → Matrix (W → Bool) (W → Bool) ℂ
  | .one U w => oneOn U w
  | .cx a b => cxOn a b

/-- The unitary of a logical circuit (gate list, head first). -/
noncomputable def logicalU {W : Type} [Fintype W] [DecidableEq W] (gs : List (LGate W)) :
    Matrix (W → Bool) (W → Bool) ℂ :=
  orderedProd (gs.map LGate.mat)

/-- A logical unitary on `LW` extended to the hardware space: identity on the system qubits outside
`sysW` and on the outside baths. -/
noncomputable def liftHw {I : Instance P} {M R : ℕ} {C : Fin P.D → ℤ} {Ccap nW : ℕ}
    (sysW : Finset (Fin I.n × Fin P.d0))
    (U : Matrix (LW I M R C Ccap nW sysW → Bool) (LW I M R C Ccap nW sysW → Bool) ℂ) :
    Matrix (HwSp I M R C Ccap nW) (HwSp I M R C Ccap nW) ℂ :=
  open Classical in
  Matrix.of fun p q =>
    if p.2 = q.2 ∧ ∀ x, x ∉ sysW → p.1 (Sum.inl x) = q.1 (Sum.inl x) then
      U (Sum.elim (fun x => p.1 (Sum.inl x.1)) (fun e => p.1 (Sum.inr e)))
        (Sum.elim (fun x => q.1 (Sum.inl x.1)) (fun e => q.1 (Sum.inr e)))
    else 0

/-- A unitary on logical qubits placed on host positions by an injective placement `pl`, identity on
the unoccupied host positions (Theorem 5.1, Eq. (35): "a connected `H_host`-qubit host containing
these registers"). -/
noncomputable def placeU {D : ℕ} {W : Type} (Hs : Finset (Fin D → ℤ)) (pl : W → {x // x ∈ Hs})
    (U : Matrix (W → Bool) (W → Bool) ℂ) :
    Matrix ({x // x ∈ Hs} → Bool) ({x // x ∈ Hs} → Bool) ℂ :=
  open Classical in
  Matrix.of fun τ' τ => if ∀ x, (∀ w, pl w ≠ x) → τ' x = τ x then U (τ' ∘ pl) (τ ∘ pl) else 0

end Supplement

end LindbladShallow



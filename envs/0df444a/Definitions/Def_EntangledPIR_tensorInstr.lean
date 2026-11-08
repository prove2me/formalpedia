-- Prove2me | Definitions.Def_EntangledPIR_tensorInstr
-- name    : EntangledPIR_tensorInstr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:45.960288+00:00
-- url     : https://prove2.me/theorems/86af9b5d-9eb1-4d2c-af13-f82bcaa69705
-- title:
--   Instruments of an honest server, acting on each copy separately
-- statement:
--   An honest server acts on each copy separately (p.25, A.1). For a finite outcome set $V$ and operators $M_c(v)$ on copy $c$ with $\sum_vM_c(v)^\dagger M_c(v)=1$, the instrument has Kraus operators $\bigotimes_cM_c(\kappa_c)\otimes1_{\mathsf R_0}$, indexed by a choice $\kappa$ of an outcome per copy, and sends a message that is a function of $\kappa$. The server leaves its other register $\mathsf R_0$ untouched. An idle server applies the identity and sends no message.
--
--   **Formalization Note** The module proves the completeness relation of these instruments, which the definition of an instrument requires.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Protocol 1, p.26; §5.2, p.25; A.1, p.53

import Definitions.Def_EntangledPIR_testProj
import Definitions.Def_EntangledPIR_Strategy
import Definitions.Def_EntangledPIR_CopyB

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), Protocol 1,
p.26, A.1, p.53: the instruments of an honest server. Honest operations act on each copy separately.
-/

open Matrix
open scoped Kronecker

namespace EntangledPIR

/-- `ICSCompute.piTensor` is multiplicative. -/
theorem piTensor_mul {ι : Type} [Fintype ι] [DecidableEq ι] {X : Type} [Fintype X]
    (O O' : ι → Matrix X X ℂ) :
    ICSCompute.piTensor (κ := fun _ => X) O * ICSCompute.piTensor (κ := fun _ => X) O' =
      ICSCompute.piTensor (κ := fun _ => X) (fun c => O c * O' c) := by
  ext p q
  simp only [Matrix.mul_apply, ICSCompute.piTensor, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib]

/-- `ICSCompute.piTensor` of the conjugate transposes. -/
theorem piTensor_conjTranspose {ι : Type} [Fintype ι] {X : Type} (O : ι → Matrix X X ℂ) :
    (ICSCompute.piTensor (κ := fun _ => X) O)ᴴ = ICSCompute.piTensor (κ := fun _ => X) (fun c => (O c)ᴴ) := by
  ext p q
  simp [ICSCompute.piTensor, Matrix.conjTranspose_apply, star_prod]

/-- The tensor product of identities is the identity. -/
theorem piTensor_one {ι : Type} [Fintype ι] {X : Type} [DecidableEq ι] [DecidableEq X] :
    ICSCompute.piTensor (κ := fun _ : ι => X) (fun _ => (1 : Matrix X X ℂ)) = 1 := by
  ext p q
  simp only [ICSCompute.piTensor, Matrix.of_apply, Matrix.one_apply]
  by_cases h : p = q
  · subst h; simp
  · obtain ⟨c, hc⟩ := Function.ne_iff.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ c) (if_neg hc)

/-- A sum over choices per copy of a product is the product of the sums. -/
theorem sum_piTensor {ι V : Type} [Fintype ι] [DecidableEq ι] [Fintype V] {X : Type}
    (M : ι → V → Matrix X X ℂ) :
    ∑ κ : ι → V, ICSCompute.piTensor (κ := fun _ => X) (fun c => M c (κ c)) =
      ICSCompute.piTensor (κ := fun _ => X) (fun c => ∑ v, M c v) := by
  ext p q
  simp only [Matrix.sum_apply, ICSCompute.piTensor, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]

/-- **An instrument of an honest server that acts on each copy separately**, on `Copies ⊗ R0`: for
outcomes `κ c`, one per copy, its Kraus operator is `⊗_c M c (κ c)` on the copies and the identity on
the register `R0` that the server leaves untouched, and its message is `out κ`. -/
noncomputable def tensorInstr {ι V X O R : Type} [Fintype ι] [DecidableEq ι] [Fintype V]
    [Fintype X] [DecidableEq X] [Fintype O] [DecidableEq O] [Fintype R] [DecidableEq R]
    (M : ι → V → Matrix X X ℂ) (h : ∀ c, ∑ v, (M c v)ᴴ * M c v = 1) (out : (ι → V) → O) :
    Instrument ((ι → X) × R) ((ι → X) × R) O where
  Idx := ι → V
  K o κ := if out κ = o then ICSCompute.piTensor (κ := fun _ => X) (fun c => M c (κ c)) ⊗ₖ (1 : Matrix R R ℂ)
    else 0
  complete := by
    rw [Finset.sum_comm]
    have h1 : ∀ κ : ι → V, ∑ o : O,
        (if out κ = o then ICSCompute.piTensor (κ := fun _ => X) (fun c => M c (κ c)) ⊗ₖ (1 : Matrix R R ℂ)
          else 0)ᴴ *
        (if out κ = o then ICSCompute.piTensor (κ := fun _ => X) (fun c => M c (κ c)) ⊗ₖ (1 : Matrix R R ℂ)
          else 0) =
        ICSCompute.piTensor (κ := fun _ => X) (fun c => (M c (κ c))ᴴ * M c (κ c)) ⊗ₖ (1 : Matrix R R ℂ) := by
      intro κ
      rw [Finset.sum_eq_single (out κ)]
      · simp only [if_true]
        rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
          Matrix.mul_one, piTensor_conjTranspose, piTensor_mul]
      · intro o _ ho
        rw [if_neg (Ne.symm ho)]
        simp
      · simp
    simp only [h1]
    have h2 : ∑ κ : ι → V,
        ICSCompute.piTensor (κ := fun _ => X) (fun c => (M c (κ c))ᴴ * M c (κ c)) ⊗ₖ (1 : Matrix R R ℂ) =
        (∑ κ : ι → V, ICSCompute.piTensor (κ := fun _ => X) (fun c => (M c (κ c))ᴴ * M c (κ c))) ⊗ₖ
          (1 : Matrix R R ℂ) := by
      ext p q
      simp [Matrix.sum_apply, Finset.sum_mul]
    rw [h2, sum_piTensor (fun c v => (M c v)ᴴ * M c v)]
    simp only [h]
    rw [piTensor_one, Matrix.one_kronecker_one]

/-- The instrument of a server that is idle in a round: it does nothing and sends no message. -/
noncomputable def idleInstr {X : Type} [Fintype X] [DecidableEq X] (L : ℕ) :
    Instrument X X (BitStr L) where
  Idx := Unit
  K o _ := if o = BitStr.ofList L [] then 1 else 0
  complete := by
    rw [Finset.sum_eq_single (BitStr.ofList L [])]
    · simp
    · intro o _ ho
      simp [ho]
    · simp

end EntangledPIR



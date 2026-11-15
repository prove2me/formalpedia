-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
-- name    : QMAPerfectCompleteness_Proof_ReversibleGadgets
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:48:11.048246+00:00
-- url     : https://prove2.me/theorems/1744602b-dedd-4573-adfc-3575527b7c6b
-- title:
--   Exact G2 reversible and phase gadgets
-- statement:
--   Defines typed X, controlled-NOT, Toffoli, paired-Hadamard, phase and triple-controlled-flip gadgets and their placement on larger registers. Matrix placement, classical permutation actions and compute-use-uncompute identities provide the physical building blocks of the block compiler.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/ReversibleGadgets.lean, retained declaration span lines 11–419.

/- Generated from Solutions.ReversibleGadgets by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates



/-! Explicit G₂ circuit gadgets used by the block-encoding compiler. -/

open Matrix
open scoped Kronecker

namespace QMAPerfectCompleteness.Main.ReversibleGadgets

/-- Place a classical operation on the selected wires and leave the others unchanged. -/
noncomputable def placePermutation {r n : ℕ} (e : Fin r ↪ Fin n)
    (σ : Basis r → Basis r) (x : Basis n) : Basis n :=
  (CircuitProof.splitTargets e).symm (σ (x ∘ e), (CircuitProof.splitTargets e x).2)

/-- A placed classical gate is exactly the permutation acting on its target wires. -/
theorem instr_classical {G : GateSet} {n : ℕ} (i : Instr G n)
    (σ : Basis (G.get i.gate).arity → Basis (G.get i.gate).arity)
    (h : (G.get i.gate).matrix = classicalMatrix σ) :
    i.matrix = classicalMatrix (placePermutation i.targets σ) := by
  classical
  ext y x
  rw [CircuitProof.instr_eq_submatrix, h]
  change (if y ∘ i.targets = σ (x ∘ i.targets) then (1 : ℂ) else 0) *
      (if (CircuitProof.splitTargets i.targets y).2 =
        (CircuitProof.splitTargets i.targets x).2 then 1 else 0) =
    if y = placePermutation i.targets σ x then 1 else 0
  have heq : y = placePermutation i.targets σ x ↔
      y ∘ i.targets = σ (x ∘ i.targets) ∧
      (CircuitProof.splitTargets i.targets y).2 = (CircuitProof.splitTargets i.targets x).2 := by
    rw [← (CircuitProof.splitTargets i.targets).apply_eq_iff_eq]
    simp only [placePermutation, Equiv.apply_symm_apply, Prod.ext_iff,
      CircuitProof.splitTargets_fst]
  simp only [heq]
  split_ifs <;> simp_all

/-- A one-wire X instruction. -/
def xAt {n : ℕ} (w : Fin n) : Instr gatesG2 n :=
  ⟨⟨0, by decide⟩, ⟨fun _ => w, by
    intro i j _
    apply Fin.ext
    have hi : i.val < 1 := i.isLt
    have hj : j.val < 1 := j.isLt
    omega⟩⟩

/-- A CNOT on a pair of distinct selected wires. -/
def cnotAt {n : ℕ} (e : Fin 2 ↪ Fin n) : Instr gatesG2 n := ⟨⟨1, by decide⟩, e⟩

/-- A Toffoli on three distinct selected wires, with target at position two. -/
def toffoliAt {n : ℕ} (e : Fin 3 ↪ Fin n) : Instr gatesG2 n := ⟨⟨2, by decide⟩, e⟩

/-- A paired Hadamard instruction. -/
noncomputable def hhAt {n : ℕ} (e : Fin 2 ↪ Fin n) : Instr gatesG2 n := ⟨⟨3, by decide⟩, e⟩

/-- A matrix for a classical map composes in the same order as gate lists. -/
theorem classicalMatrix_mul {n : ℕ} (f g : Basis n → Basis n) :
    classicalMatrix g * classicalMatrix f = classicalMatrix (g ∘ f) := by
  classical
  ext y x
  simp [Matrix.mul_apply, classicalMatrix, mul_ite]

/-- The basis action of a Toffoli at arbitrary distinct wire addresses. -/
def toffoliAction {n : ℕ} (e : Fin 3 ↪ Fin n) (x : Basis n) : Basis n :=
  Function.update x (e 2) (xor (x (e 2)) (x (e 0) && x (e 1)))

theorem place_toffoli {n : ℕ} (e : Fin 3 ↪ Fin n) (x : Basis n) :
    placePermutation e (fun a => ![a 0, a 1, xor (a 2) (a 0 && a 1)]) x =
      toffoliAction e x := by
  classical
  apply (CircuitProof.splitTargets e).injective
  simp only [placePermutation, Equiv.apply_symm_apply]
  apply Prod.ext
  · funext j
    fin_cases j <;>
      simp [CircuitProof.splitTargets_fst, toffoliAction, Function.update_of_ne,
        e.injective.ne (by decide : (0 : Fin 3) ≠ 2),
        e.injective.ne (by decide : (1 : Fin 3) ≠ 2)]
  · funext w
    have hw : (w : Fin n) ≠ e 2 := by
      intro h
      exact w.2 ⟨2, h.symm⟩
    simp [CircuitProof.splitTargets_snd, toffoliAction, Function.update_of_ne hw]

/-- Exact matrix semantics of a placed Toffoli instruction. -/
theorem toffoliAt_matrix {n : ℕ} (e : Fin 3 ↪ Fin n) :
    (toffoliAt e).matrix = classicalMatrix (toffoliAction e) := by
  rw [instr_classical (toffoliAt e) _ rfl]
  congr 1
  funext x
  exact place_toffoli e x

/-- Three controls on wires 0,1,2, target wire 3, and one clean scratch wire 4. -/
def tripleControlledX : List (Instr gatesG2 5) :=
  [toffoliAt ⟨![0,1,4], by decide⟩,
    toffoliAt ⟨![4,2,3], by decide⟩,
    toffoliAt ⟨![0,1,4], by decide⟩]



/-- The five-wire gadget computes a three-controlled X and returns its initially-zero scratch
wire to zero. The equality is a statement about the full output basis state. -/
theorem tripleControlledX_matrix (y x : Basis 5) (hclean : x 4 = false) :
    circuitMatrix tripleControlledX y x =
      if y = Function.update x 3 (xor (x 3) ((x 0 && x 1) && x 2)) then 1 else 0 := by
  classical
  simp only [tripleControlledX, circuitMatrix, Matrix.one_mul, toffoliAt_matrix,
    classicalMatrix_mul]
  have heval : toffoliAction ⟨![0,1,4], by decide⟩
      (toffoliAction ⟨![4,2,3], by decide⟩
        (toffoliAction ⟨![0,1,4], by decide⟩ x)) =
      Function.update x 3 (xor (x 3) ((x 0 && x 1) && x 2)) := by
    funext w
    fin_cases w <;> simp [toffoliAction, hclean]
  simpa only [classicalMatrix, Matrix.of_apply, Function.comp_apply, heval]

/-- The sign gadget acts on its first wire and leaves the second wire as a clean spectator. -/
noncomputable def phaseZ : List (Instr gatesG2 2) :=
  [hhAt (Function.Embedding.refl _), xAt 0, hhAt (Function.Embedding.refl _)]



/-- The basis action of X at an arbitrary wire address. -/
def xAction {n : ℕ} (w : Fin n) (x : Basis n) : Basis n := Function.update x w (!x w)

theorem xAt_matrix {n : ℕ} (w : Fin n) :
    (xAt w).matrix = classicalMatrix (xAction w) := by
  rw [instr_classical (xAt w) _ rfl]
  congr 1
  funext x
  let e : Fin 1 ↪ Fin n := (xAt w).targets
  change placePermutation e (fun a : Basis 1 => ![!a 0]) x = xAction w x
  apply (CircuitProof.splitTargets e).injective
  simp only [placePermutation, Equiv.apply_symm_apply]
  apply Prod.ext
  · funext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    change (!x w) = Function.update x w (!x w) w
    simp
  · funext j
    have hj : (j : Fin n) ≠ w := by
      intro h
      have hew : e (0 : Fin 1) = w := rfl
      exact j.2 ⟨(0 : Fin 1), hew.trans h.symm⟩
    change x (j : Fin n) = Function.update x w (!x w) (j : Fin n)
    rw [Function.update_of_ne hj]







/-- Place an entire local matrix on selected wires, with identity on untouched wires. -/
noncomputable def placeMatrix {r n : ℕ} (e : Fin r ↪ Fin n)
    (A : Matrix (Basis r) (Basis r) ℂ) : Matrix (Basis n) (Basis n) ℂ :=
  (A ⊗ₖ (1 : Matrix ({w : Fin n // w ∉ Set.range e} → Bool)
    ({w : Fin n // w ∉ Set.range e} → Bool) ℂ)).submatrix
      (CircuitProof.splitTargets e) (CircuitProof.splitTargets e)

theorem placeMatrix_apply {r n : ℕ} (e : Fin r ↪ Fin n)
    (A : Matrix (Basis r) (Basis r) ℂ) (y x : Basis n) :
    placeMatrix e A y x =
      if (∀ w, (∀ a, e a ≠ w) → y w = x w) then A (y ∘ e) (x ∘ e) else 0 := by
  classical
  change A (y ∘ e) (x ∘ e) *
    (if (CircuitProof.splitTargets e y).2 = (CircuitProof.splitTargets e x).2 then 1 else 0) =
      if (∀ w, (∀ a, e a ≠ w) → y w = x w) then A (y ∘ e) (x ∘ e) else 0
  split_ifs with hcomp hmask hmask
  · exact mul_one _
  · exact (hmask ((CircuitProof.unaffected_iff e x y).mpr hcomp)).elim
  · exact (hcomp ((CircuitProof.unaffected_iff e x y).mp hmask)).elim
  · exact mul_zero _

theorem placeMatrix_one {r n : ℕ} (e : Fin r ↪ Fin n) :
    placeMatrix e (1 : Matrix (Basis r) (Basis r) ℂ) = 1 := by
  classical
  simp [placeMatrix, Matrix.one_kronecker_one]

theorem placeMatrix_mul {r n : ℕ} (e : Fin r ↪ Fin n)
    (A B : Matrix (Basis r) (Basis r) ℂ) :
    placeMatrix e (A * B) = placeMatrix e A * placeMatrix e B := by
  classical
  simp only [placeMatrix]
  rw [Matrix.submatrix_mul_equiv _ _ (CircuitProof.splitTargets e)
    (CircuitProof.splitTargets e) (CircuitProof.splitTargets e),
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- Relabeling instruction targets is the same as placing its local matrix. -/
theorem instr_mapWires_matrix {G : GateSet} {r n : ℕ} (e : Fin r ↪ Fin n) (i : Instr G r) :
    (i.mapWires e).matrix = placeMatrix e i.matrix := by
  classical
  ext y x
  rw [placeMatrix_apply]
  have hiff :
      (∀ w, (∀ a, e (i.targets a) ≠ w) → y w = x w) ↔
      (∀ w, (∀ a, e a ≠ w) → y w = x w) ∧
      (∀ w, (∀ a, i.targets a ≠ w) → y (e w) = x (e w)) := by
    constructor
    · intro h
      constructor
      · intro w hw
        exact h w (fun a => hw (i.targets a))
      · intro w hw
        exact h (e w) (fun a heq => hw a (e.injective heq))
    · rintro ⟨he, hi⟩ w hw
      by_cases hr : w ∈ Set.range e
      · obtain ⟨j, rfl⟩ := hr
        exact hi j (fun a h => hw a (congrArg e h))
      · exact he w (fun a h => hr ⟨a,h⟩)
  change (if (∀ w, (∀ a, e (i.targets a) ≠ w) → y w = x w) then
      (G.get i.gate).matrix ((y ∘ e) ∘ i.targets) ((x ∘ e) ∘ i.targets) else 0) =
    if (∀ w, (∀ a, e a ≠ w) → y w = x w) then
      (if (∀ w, (∀ a, i.targets a ≠ w) → y (e w) = x (e w)) then
        (G.get i.gate).matrix ((y ∘ e) ∘ i.targets) ((x ∘ e) ∘ i.targets) else 0) else 0
  simp only [hiff, ite_and]

/-- Any verified local gate list can be moved to arbitrary distinct wire addresses. -/
theorem circuitMatrix_mapWires {G : GateSet} {r n : ℕ} (e : Fin r ↪ Fin n)
    (gs : List (Instr G r)) :
    circuitMatrix (gs.map (Instr.mapWires e)) = placeMatrix e (circuitMatrix gs) := by
  induction gs with
  | nil => simp [circuitMatrix, placeMatrix_one]
  | cons g gs ih =>
    simp only [List.map_cons, circuitMatrix, ih, instr_mapWires_matrix, placeMatrix_mul]

/-- The exact sign gadget on arbitrary selected wires. -/
noncomputable def phaseZAt {n : ℕ} (e : Fin 2 ↪ Fin n) : List (Instr gatesG2 n) :=
  phaseZ.map (Instr.mapWires e)





/-- The triple-controlled flag flip at arbitrary selected wire addresses. -/
noncomputable def tripleControlledXAt {n : ℕ} (e : Fin 5 ↪ Fin n) : List (Instr gatesG2 n) :=
  tripleControlledX.map (Instr.mapWires e)







/-- Updating a selected local bit is exactly updating that wire in the full register. -/
theorem place_update {r n : ℕ} (e : Fin r ↪ Fin n) (j : Fin r)
    (f : Basis r → Bool) (x : Basis n) :
    placePermutation e (fun a => Function.update a j (f a)) x =
      Function.update x (e j) (f (x ∘ e)) := by
  classical
  apply (CircuitProof.splitTargets e).injective
  simp only [placePermutation, Equiv.apply_symm_apply]
  apply Prod.ext
  · funext a
    change Function.update (x ∘ e) j (f (x ∘ e)) a =
      Function.update x (e j) (f (x ∘ e)) (e a)
    by_cases h : a = j
    · subst a
      simp
    · simp [Function.update_of_ne h, Function.update_of_ne (e.injective.ne h)]
  · funext w
    have hw : (w : Fin n) ≠ e j := by
      intro h
      exact w.2 ⟨j,h.symm⟩
    change x (w : Fin n) = Function.update x (e j) (f (x ∘ e)) (w : Fin n)
    rw [Function.update_of_ne hw]

/-- Full-register clean-workspace semantics of the three-controlled flag flip. -/
theorem tripleControlledXAt_matrix {n : ℕ} (e : Fin 5 ↪ Fin n) (y x : Basis n)
    (hclean : x (e 4) = false) :
    circuitMatrix (tripleControlledXAt e) y x =
      if y = Function.update x (e 3)
        (xor (x (e 3)) ((x (e 0) && x (e 1)) && x (e 2))) then 1 else 0 := by
  classical
  rw [tripleControlledXAt, circuitMatrix_mapWires, placeMatrix_apply,
    tripleControlledX_matrix _ _ hclean]
  let σ : Basis 5 → Basis 5 := fun a =>
    Function.update a 3 (xor (a 3) ((a 0 && a 1) && a 2))
  have hiff :
      (∀ w, (∀ a, e a ≠ w) → y w = x w) ∧ y ∘ e = σ (x ∘ e) ↔
        y = placePermutation e σ x := by
    rw [← (CircuitProof.splitTargets e).apply_eq_iff_eq]
    simp only [placePermutation, Equiv.apply_symm_apply, Prod.ext_iff,
      CircuitProof.splitTargets_fst]
    rw [CircuitProof.unaffected_iff e x y]
    exact and_comm
  change (if (∀ w, (∀ a, e a ≠ w) → y w = x w) then
      if y ∘ e = σ (x ∘ e) then (1 : ℂ) else 0 else 0) = _
  rw [← ite_and]
  simp only [hiff]
  rw [place_update]
  rfl

/-- The literal compute/use/uncompute list used for clean reversible predicates. -/
noncomputable def computeUseUncompute {n : ℕ} (compute use : List (Instr gatesG2 n)) :
    List (Instr gatesG2 n) := compute ++ use ++ compute.reverse



theorem computeUseUncompute_matrix {n : ℕ} (compute use : List (Instr gatesG2 n)) :
    circuitMatrix (computeUseUncompute compute use) =
      (circuitMatrix compute)ᴴ * circuitMatrix use * circuitMatrix compute := by
  simp only [computeUseUncompute, BlockProof.circuitMatrix_append,
    BlockProof.circuitMatrix_reverse_g2, Matrix.mul_assoc]









/-- A circuit realizing a deterministic classical map must realize an injective map, since all
placed G₂ instructions are unitary. This discharges the injectivity premise for phase kickback. -/
theorem classicalCircuit_injective {n : ℕ} (gs : List (Instr gatesG2 n))
    (f : Basis n → Basis n) (hgs : circuitMatrix gs = classicalMatrix f) :
    Function.Injective f := by
  classical
  have hu := Matrix.mem_unitaryGroup_iff'.mp (CircuitProof.circuit_unitary gs)
  rw [hgs] at hu
  intro x y hxy
  by_contra hne
  have hentry := congrArg (fun M : Matrix (Basis n) (Basis n) ℂ => M x y) hu
  have hbad : (1 : ℂ) = 0 := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, classicalMatrix,
      ite_mul, mul_ite, hxy, hne] using hentry
  norm_num at hbad



end QMAPerfectCompleteness.Main.ReversibleGadgets



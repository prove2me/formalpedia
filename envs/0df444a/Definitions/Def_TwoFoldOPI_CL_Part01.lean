-- Prove2me | Definitions.Def_TwoFoldOPI_CL_Part01
-- name    : TwoFoldOPI_CL_Part01
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-11T17:42:03.649514+00:00
-- url     : https://prove2.me/theorems/3663fdbc-5313-4ad1-b55a-90bfe0d67ae0
-- title:
--   Construction for Theorem 7.4, part 1: program semantics, reversible gates and gadgets
-- statement:
--   Definitions underlying the formal construction behind the algorithmic part of Theorem 7.4 (two-fold OPI variant). This part sets up the semantics of oracle-free adaptive membership programs (gates, measurements, preparations, classical memory) and the reversible-circuit toolkit used throughout: Toffoli and multi-controlled gates, relocation of circuits along wire embeddings, phase kickback, adders and increments, lookups and permutation gadgets, the $\mathrm{QFT}_p$ and $\mathrm{QFT}_q$ gadgets with their phase tables, the symbol encoding of field elements, the straight-line (SSA) compilation of field programs and the Gaussian-elimination program used by the classical decoder of the Schur-square relinearization.
--
--   The bundle contains only definitions together with the structural lemmas that these definitions require (lemmas cited inside definitions, lemmas appearing in statements of later results, and `simp` lemmas).
-- source:
--   Formalization of Theorem 7.4 (algorithmic part), repository https://github.com/sragavan99/lean-prove2me-fills/blob/db81d0d4e3fa008609ed37789a2eb2f6f08ee48d/Definitions/Def_TwoFoldOPI_CL_Part01.lean

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Defs_OPIOraclePrograms
import Definitions.Def_QAlgorithms_Defs_OPIUniformity
import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_TwoFoldOPI_elemBits
import Definitions.Def_TwoFoldOPI_schurSquare
import Definitions.Def_TwoFoldOPI_schurFailureSum

set_option maxHeartbeats 400000
set_option linter.all false

-- ===== OPI.Embed =====
section

/-!
# M2 core: algebra of `embedOp`

`embedOp M w` is the reindexing of `M ⊗ 1` along the splitting of a basis string into its
`w`-part and its outside part. All algebraic properties follow from this description.
-/

namespace OPI

open QAlgorithms Matrix

open scoped Kronecker

variable {k n : ℕ}

/-- The wires outside the range of `w`. -/
abbrev Outside (w : Fin k ↪ Fin n) := {a : Fin n // a ∉ Set.range w}

open Classical in
/-- Splitting a basis string into the part on `w` and the part outside. -/
noncomputable def splitEquiv (w : Fin k ↪ Fin n) :
    Qubits n ≃ Qubits k × (Outside w → Bool) :=
  (Equiv.piEquivPiSubtypeProd (· ∈ Set.range w) (fun _ => Bool)).trans
    (Equiv.prodCongr
      (Equiv.arrowCongr (Equiv.ofInjective w w.injective).symm (Equiv.refl Bool))
      (Equiv.refl _))

@[simp] lemma splitEquiv_fst (w : Fin k ↪ Fin n) (y : Qubits n) :
    (splitEquiv w y).1 = y ∘ w := by
  funext i
  simp only [splitEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_fst,
    Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.refl_apply, Function.comp_apply]
  rfl

@[simp] lemma splitEquiv_snd (w : Fin k ↪ Fin n) (y : Qubits n) :
    (splitEquiv w y).2 = fun o => y o.1 := by
  funext o
  rfl

















/-! ### Single-qubit and two-qubit gates -/

/-- The bijection `Qubits 1 ≃ Bool`. -/
def q1Equiv : Qubits 1 ≃ Bool where
  toFun b := b 0
  invFun x := fun _ => x
  left_inv b := by funext i; fin_cases i; rfl
  right_inv x := rfl

/-- The bijection `Qubits 2 ≃ Bool × Bool`. -/
def q2Equiv : Qubits 2 ≃ Bool × Bool where
  toFun b := (b 0, b 1)
  invFun x := ![x.1, x.2]
  left_inv b := by funext i; fin_cases i <;> rfl
  right_inv x := rfl















/-! ### Circuits -/









end OPI
end

-- ===== OPI.Sem =====
section

/-!
# M1: semantics of adaptive membership programs

Every leaf of `adaptiveExecution` is `ρ ↦ Σ_j K_j ρ K_jᴴ` for a list of Kraus operators that does
not depend on `ρ`; the branch structure depends only on the classical memory. Consequences:
linearity, positivity, trace preservation, and error bounds for output laws.
-/

namespace OPI

open QAlgorithms QAlgorithms.OPI Matrix

open scoped ComplexOrder

variable {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {ctl : Fin r → Bool} {N c out : ℕ}

/-- Square matrices on `N` qubits. -/
abbrev Mat (N : ℕ) := Matrix (Qubits N) (Qubits N) ℂ

/-- `ρ ↦ Σ_{K ∈ Ks} K ρ Kᴴ`. -/
noncomputable def sandwich (Ks : List (Mat N)) (ρ : Mat N) : Mat N :=
  (Ks.map fun K => K * ρ * Kᴴ).sum

/-- The value computed by a classical `boolean` instruction. -/
def boolVal (op : BoolOp) {c : ℕ} (mem : Fin c → Bool) (x y : Fin c) : Bool :=
  match op with | .and => mem x && mem y | .or => mem x || mem y | .not => !mem x

/-- The Kraus skeleton of an execution: one entry per leaf, with output, Kraus operators and
counts. -/
noncomputable def execKraus (O : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    AdaptiveMembershipProgram S a ctl N c out → (Fin c → Bool) →
      List (Option (Fin out → Bool) × List (Mat N) × (Fin 5 → ℕ))
  | .halt D _, mem => [(some (D.eval mem), [1], fun j => if j = 4 then D.size else 0)]
  | .fail, _ => [(none, [1], 0)]
  | .gate g next, mem => (execKraus O next mem).map fun t =>
      (t.1, t.2.1.map (· * embedOp g.gate.mat g.wires), t.2.2 + Pi.single 1 1)
  | .query k adj control _ w hc next, mem => (execKraus O next mem).map fun t =>
      (t.1, t.2.1.map (· * OracleStep.mat (S := S) O (.query k adj control w hc)),
        t.2.2 + Pi.single 0 1)
  | .measure q dst next, mem => [false, true].flatMap fun b =>
      (execKraus O (next b) (Function.update mem dst b)).map fun t =>
        (t.1, t.2.1.map (· * qubitOp1 (measProj b) q), t.2.2 + Pi.single 3 1)
  | .prepare q next, mem => (execKraus O next mem).map fun t =>
      (t.1, t.2.1.flatMap (fun K => [K * qubitOp1 (resetKraus false) q,
        K * qubitOp1 (resetKraus true) q]), t.2.2 + Pi.single 2 1)
  | .coin dst next, mem => [false, true].flatMap fun b =>
      (execKraus O (next b) (Function.update mem dst b)).map fun t =>
        (t.1, t.2.1.map (· * (((Real.sqrt 2 : ℂ))⁻¹ • (1 : Mat N))), t.2.2 + Pi.single 4 1)
  | .setBit dst b next, mem => (execKraus O next (Function.update mem dst b)).map fun t =>
      (t.1, t.2.1, t.2.2 + Pi.single 4 1)
  | .boolean op dst x y next, mem =>
      (execKraus O next (Function.update mem dst (boolVal op mem x y))).map fun t =>
        (t.1, t.2.1, t.2.2 + Pi.single 4 1)
  | .branch src next, mem => (execKraus O (next (mem src)) mem).map fun t =>
      (t.1, t.2.1, t.2.2 + Pi.single 4 1)

/-! ### Sandwich algebra -/

@[simp] lemma sandwich_nil (ρ : Mat N) : sandwich [] ρ = 0 := rfl

@[simp] lemma sandwich_one (ρ : Mat N) : sandwich [1] ρ = ρ := by
  simp [sandwich]

















/-! ### Completeness of the Kraus family -/

/-- `Σ_{K ∈ Ks} Kᴴ K`. -/
noncomputable def innerSum (Ks : List (Mat N)) : Mat N := (Ks.map fun K => Kᴴ * K).sum

/-- `Σ_t Σ_{K ∈ t} Kᴴ K` over a skeleton. -/
noncomputable def kSum {α β : Type*} (L : List (α × List (Mat N) × β)) : Mat N :=
  (L.map fun t => innerSum t.2.1).sum





























/-! ### Traces, laws and the effect bound -/







open Classical in
/-- The probability of `event` when the program starts from the cq-state `(ρ, mem)`. -/
noncomputable def lawFrom (O : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (P : AdaptiveMembershipProgram S a ctl N c out) (event : Option (Fin out → Bool) → Prop)
    (ρ : Mat N) (mem : Fin c → Bool) : ℝ :=
  ((adaptiveExecution O P ρ mem).map fun leaf =>
    if event leaf.1.1 then leaf.1.2.trace.re else 0).sum



















/-! ### Resources -/





end OPI
end

-- ===== OPI.Ser =====
section

/-!
# M0: shared-node serialization

* `programNodeTable` is *stable*: a table produced by it already contains the program, and
  re-serializing on any extension of that table changes nothing.
* Programs are generated as DAGs (`Node` lists whose children point to earlier indices); the
  memoized traversal `trav` computes `programNodeTable` of the unfolded tree in polynomial time.
-/

namespace OPI

open QAlgorithms QAlgorithms.OPI QAlgorithms.Complexity

/-! ### Stability of interning -/

/-- A table transformer that only appends and is idempotent on its own output. -/
def GoodF (pn : List Str → ℕ × List Str) : Prop :=
  ∀ T, (∃ V, (pn T).2 = T ++ V) ∧ ∀ U, pn ((pn T).2 ++ U) = ((pn T).1, (pn T).2 ++ U)











section
variable {r : ℕ} {a : Fin r → ℕ} {ctl : Fin r → Bool} {N c out : ℕ}



end

/-! ### DAG programs and memoized serialization -/

/-- A node of a DAG program; children are indices of earlier nodes. -/
inductive Node (N c out : ℕ) where
  | halt (D : BoolCircuit c out) (valid : D.WellFormed)
  | fail
  | gate (g : GateApp htcxGateSet N) (j : ℕ)
  | measure (q : Fin N) (dst : Fin c) (j0 j1 : ℕ)
  | prepare (q : Fin N) (j : ℕ)
  | coin (dst : Fin c) (j0 j1 : ℕ)
  | setBit (dst : Fin c) (b : Bool) (j : ℕ)
  | boolean (op : BoolOp) (dst x y : Fin c) (j : ℕ)
  | branch (src : Fin c) (j0 j1 : ℕ)

section DAG
variable {r : ℕ} {a : Fin r → ℕ} {ctl : Fin r → Bool} {N c out : ℕ}



end DAG

/-- Node codes, exactly as in `programNodeTable`. -/
def haltCode {c out : ℕ} (D : BoolCircuit c out) : Str :=
  serializeWords [0, D.gates.length] ++
    (D.gates.flatMap fun g => serializeWords [Learning.boolOpCode g.op, g.a, g.b]) ++
    serializeWords (List.ofFn D.outputs)



/-- The code of the `fail` node. -/
def failCode : Str := serializeWords [1]

section Trav
variable {N c out : ℕ}

/-- Result triple of the traversal: index, table, memo. -/
abbrev TravRes := ℕ × List Str × (ℕ → Option ℕ)



end Trav

section TravSpec
variable {r : ℕ} {a : Fin r → ℕ} {ctl : Fin r → Bool} {N c out : ℕ}



















end TravSpec

end OPI
end

-- ===== OPI.Build =====
section

/-!
# M0: building DAG programs from segments

A segment is a continuation transformer on oracle-free programs together with a DAG builder;
`Seg.Valid` says that the builder realizes the transformer. Validity is closed under the
combinators below, so a generator that composes segments produces a DAG whose unfolding is the
composed program.
-/

namespace OPI

open QAlgorithms QAlgorithms.OPI QAlgorithms.Complexity

/-- Oracle-free programs over `{H, T, CNOT}` (the shape of `TwoFoldOPI.acceptProb`). -/
abbrev Prog (N c out : ℕ) :=
  AdaptiveMembershipProgram htcxGateSet (fun _ : Fin 0 => 0) (fun _ => false) N c out

variable {N c out : ℕ}





/-- A segment: a DAG builder (continuation index ↦ entry index) and its tree semantics. -/
structure Seg (N c out : ℕ) where
  build : ℕ → List (Node N c out) → ℕ × List (Node N c out)
  prog : Prog N c out → Prog N c out



/-- Emit one node. -/
def emit (nd : Node N c out) (dag : List (Node N c out)) : ℕ × List (Node N c out) :=
  (dag.length, dag ++ [nd])







/-! ### Primitive segments -/

/-- One gate. -/
def gateSeg (g : GateApp htcxGateSet N) : Seg N c out :=
  ⟨fun k dag => emit (.gate g k) dag, fun P => .gate g P⟩











/-- The empty segment. -/
def idSeg : Seg N c out := ⟨fun k dag => (k, dag), id⟩

/-- Sequential composition: `s₁` then `s₂`. -/
def Seg.comp (s₁ s₂ : Seg N c out) : Seg N c out :=
  ⟨fun k dag => s₁.build (s₂.build k dag).1 (s₂.build k dag).2, fun P => s₁.prog (s₂.prog P)⟩



section
variable {s s₀ s₁ s₂ : Seg N c out}























end

end OPI
end

-- ===== OPI.Laws =====
section

/-!
# Closing segments into packed programs; step equations for output laws
-/

namespace OPI

open QAlgorithms QAlgorithms.OPI QAlgorithms.Complexity Matrix

variable {N c out : ℕ}









/-! ### Law equations, one instruction at a time -/

section
variable {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {ctl : Fin r → Bool}
variable (O : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
variable (event : Option (Fin out → Bool) → Prop)

















end

/-! ### Circuit segments -/

/-- The segment applying a circuit, first gate first. -/
def circSeg : Circuit htcxGateSet N → Seg N c out
  | [] => idSeg
  | g :: C => (gateSeg g).comp (circSeg C)





end OPI
end

-- ===== OPI.Gates =====
section

/-!
# M3 base: exact gates over `{H, T, CNOT}` and the phase-permutation calculus

`phPerm π e` is the matrix `|z⟩ ↦ ω^{e z} |π z⟩` with `ω = e^{iπ/4}` and `e z ∈ ZMod 8`.
Products of such matrices are again of this form, so chains of `T` and `CNOT` gates reduce to
finite checks on bit strings.
-/

namespace OPI

open QAlgorithms Matrix

variable {N : ℕ}

/-- `ω = e^{iπ/4}`. -/
noncomputable def ω8 : ℂ := Complex.exp (Complex.I * Real.pi / 4)





/-- `ω^e` for `e ∈ ZMod 8`. -/
noncomputable def ωz (e : ZMod 8) : ℂ := ω8 ^ e.val



@[simp] lemma ωz_zero : ωz 0 = 1 := by simp [ωz]





/-- The phase-permutation matrix `|z⟩ ↦ ω^{e z} |π z⟩`. -/
noncomputable def phPerm (π : Qubits N → Qubits N) (e : Qubits N → ZMod 8) : Mat N :=
  Matrix.of fun y z => if y = π z then ωz (e z) else 0







/-! ### Single-wire embeddings -/



















/-! ### CNOT -/










/-! ### Gate applications -/

/-- `H` on wire `q`. -/
noncomputable def hApp (q : Fin N) : GateApp htcxGateSet N :=
  ⟨Gate.ofMatrix1 QAlgorithms.hadamard, Or.inl rfl, Stabilizer.wire1 q⟩

/-- `T` on wire `q`. -/
noncomputable def tApp (q : Fin N) : GateApp htcxGateSet N :=
  ⟨Gate.ofMatrix1 gateT, Or.inr (Or.inl rfl), Stabilizer.wire1 q⟩

/-- `CNOT` with control `c`, target `t`. -/
def cxApp (c t : Fin N) (h : c ≠ t) : GateApp htcxGateSet N :=
  ⟨Gate.ofMatrix2 cnot, Or.inr (Or.inr rfl), Stabilizer.wire2 c t h⟩

/-- Phase gates: `T` and `CNOT`. -/
inductive PGate (N : ℕ) where
  | t (q : Fin N)
  | cx (c t : Fin N) (h : c ≠ t)

namespace PGate

/-- The gate application. -/
noncomputable def app : PGate N → GateApp htcxGateSet N
  | .t q => tApp q
  | .cx c tt h => cxApp c tt h

/-- The basis permutation. -/
def perm : PGate N → Qubits N → Qubits N
  | .t _ => id
  | .cx c tt _ => fun z => Function.update z tt (xor (z tt) (z c))

/-- The phase exponent. -/
def exp : PGate N → Qubits N → ZMod 8
  | .t q => fun z => if z q then 1 else 0
  | .cx _ _ _ => 0



end PGate

/-- Composite permutation of a phase circuit (first gate first). -/
def pcPerm : List (PGate N) → Qubits N → Qubits N
  | [] => id
  | g :: L => pcPerm L ∘ g.perm

/-- Composite phase exponent of a phase circuit. -/
def pcExp : List (PGate N) → Qubits N → ZMod 8
  | [] => 0
  | g :: L => fun z => g.exp z + pcExp L (g.perm z)



end OPI
end

-- ===== OPI.Toffoli =====
section

/-! # M3: exact Toffoli over `{H, T, CNOT}` (the 37-gate circuit of N&C Fig. 4.9) -/

namespace OPI

open QAlgorithms Matrix

variable {N : ℕ}

















section Tof
variable (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)

/-- The phase part of the Toffoli circuit. -/
def tofChain : List (PGate N) :=
  ([.t p, .t q, .t r, .cx p q hpq] ++ List.replicate 7 (.t q)) ++
  ([.cx p q hpq, .cx q r hqr] ++ List.replicate 7 (.t r)) ++
  ([.cx q r hqr, .cx p r hpr] ++ List.replicate 7 (.t r)) ++
  [.cx p r hpr, .cx p r hpr, .cx q r hqr, .t r, .cx q r hqr, .cx p r hpr]

/-- The Toffoli circuit, controls `p, q`, target `r` (37 gates). -/
noncomputable def tofCirc : Circuit htcxGateSet N :=
  [hApp r] ++ (tofChain p q r hpq hpr hqr).map PGate.app ++ [hApp r]









end Tof

end OPI
end

-- ===== OPI.Rev =====
section

/-!
# M3: classical reversible circuits

`RGate` = X / CNOT / Toffoli with their action on bit strings. A list of reversible gates
compiles to an exact `{H, T, CNOT}` circuit whose unitary is the permutation matrix of the
action. From here on classical gadgets are verified as Boolean functions.
-/

namespace OPI

open QAlgorithms Matrix

variable {N : ℕ}

/-- Reversible gates. -/
inductive RGate (N : ℕ) where
  | x (q : Fin N)
  | cx (c t : Fin N)
  | ccx (a b t : Fin N)

namespace RGate

/-- Action on bit strings. -/
def act : RGate N → Qubits N → Qubits N
  | .x q => fun z => Function.update z q (!z q)
  | .cx c tt => fun z => if c ≠ tt then Function.update z tt (xor (z tt) (z c)) else z
  | .ccx a b tt => fun z =>
      if a ≠ b ∧ a ≠ tt ∧ b ≠ tt then Function.update z tt (xor (z tt) (z a && z b)) else z

/-- Compilation to `{H, T, CNOT}`. -/
noncomputable def circ : RGate N → Circuit htcxGateSet N
  | .x q => [hApp q] ++ (List.replicate 4 (PGate.t q)).map PGate.app ++ [hApp q]
  | .cx c tt => if h : c ≠ tt then [cxApp c tt h] else []
  | .ccx a b tt => if h : a ≠ b ∧ a ≠ tt ∧ b ≠ tt then tofCirc a b tt h.1 h.2.1 h.2.2 else []





lemma act_act (g : RGate N) (z : Qubits N) : g.act (g.act z) = z := by
  cases g with
  | x q => funext i; by_cases h : i = q
           · subst h; simp [act]
           · simp [act, Function.update_of_ne h]
  | cx c tt =>
    by_cases h : c ≠ tt
    · simp only [act, if_pos h]
      funext i; by_cases hi : i = tt
      · subst hi; simp [Function.update_of_ne h]
      · simp [Function.update_of_ne hi]
    · simp only [act, if_neg h]
  | ccx a b tt =>
    by_cases h : a ≠ b ∧ a ≠ tt ∧ b ≠ tt
    · simp only [act, if_pos h]
      funext i; by_cases hi : i = tt
      · subst hi; simp [Function.update_of_ne h.2.1, Function.update_of_ne h.2.2]
      · simp [Function.update_of_ne hi]
    · simp only [act, if_neg h]

end RGate

/-- Action of a reversible circuit (first gate first). -/
def revAct : List (RGate N) → Qubits N → Qubits N
  | [] => id
  | g :: L => revAct L ∘ g.act

/-- Compilation of a reversible circuit. -/
noncomputable def revCirc (L : List (RGate N)) : Circuit htcxGateSet N := L.flatMap RGate.circ



lemma revAct_append (L₁ L₂ : List (RGate N)) : revAct (L₁ ++ L₂) = revAct L₂ ∘ revAct L₁ := by
  induction L₁ with
  | nil => rfl
  | cons g L ih => simp only [List.cons_append, revAct, ih]; rfl

/-- The reversed circuit undoes the circuit. -/
lemma revAct_reverse (L : List (RGate N)) (z : Qubits N) : revAct L.reverse (revAct L z) = z := by
  induction L generalizing z with
  | nil => rfl
  | cons g L ih =>
    rw [List.reverse_cons, revAct_append]
    simp only [revAct, Function.comp_apply, id]
    rw [ih, RGate.act_act]

lemma revAct_reverse' (L : List (RGate N)) (z : Qubits N) : revAct L (revAct L.reverse z) = z := by
  have := revAct_reverse L.reverse z
  rwa [List.reverse_reverse] at this



end OPI
end

-- ===== OPI.MCX =====
section

/-! # M3: multi-controlled X with clean ancillas (Toffoli ladder) -/

namespace OPI

open QAlgorithms

variable {N : ℕ}

/-- Flip `t` iff all wires `cs` are set; uses ancillas from `as` (initially clean). -/
def mcx : List (Fin N) → List (Fin N) → Fin N → List (RGate N)
  | [], _, t => [.x t]
  | [c], _, t => [.cx c t]
  | [c1, c2], _, t => [.ccx c1 c2 t]
  | c1 :: c2 :: c3 :: cs, a :: as, t =>
      .ccx c1 c2 a :: (mcx (a :: c3 :: cs) as t ++ [.ccx c1 c2 a])
  | _ :: _ :: _ :: _, [], _ => []









end OPI
end

-- ===== OPI.Reloc =====
section

/-! # M2: relocating circuits along wire embeddings -/

namespace OPI

open QAlgorithms Matrix

variable {k m n : ℕ}



/-- Place a gate application along `w`. -/
def relocApp {S : Set Gate} (w : Fin m ↪ Fin n) (g : GateApp S m) : GateApp S n :=
  ⟨g.gate, g.mem, g.wires.trans w⟩

/-- Place a circuit along `w`. -/
def relocCirc {S : Set Gate} (w : Fin m ↪ Fin n) (C : Circuit S m) : Circuit S n :=
  C.map (relocApp w)





end OPI
end

-- ===== OPI.Kickback =====
section

/-!
# M4: phase kickback from the gradient register

`gradVec b` is `2^{-b/2} Σ_g e^{-2πi g/2^b} |g⟩`. Adding a value `v` (computed from the other
wires) into the gradient register multiplies the state by `e^{2πi v/2^b}` and leaves the gradient
register unchanged.
-/

namespace OPI

open QAlgorithms Matrix

variable {N b : ℕ}

lemma bitsToNat_lt (g : Qubits b) : bitsToNat g < 2 ^ b := by
  rw [← bitsEquivFin_apply]; exact (bitsEquivFin b g).isLt

lemma bitsToNat_natToBits (k : ℕ) : bitsToNat (natToBits b k) = k % 2 ^ b := by
  rw [← bitsEquivFin_apply, natToBits, Equiv.apply_symm_apply]

/-- Addition mod `2^b` on `b`-bit registers. -/
def addBits (v : ℕ) (g : Qubits b) : Qubits b := natToBits b ((bitsToNat g + v) % 2 ^ b)

lemma addBits_arith (M G v : ℕ) (hM : 0 < M) (hG : G < M) :
    ((G + v) % M + (M - v % M)) % M = G ∧ ((G + (M - v % M)) % M + v) % M = G := by
  have hvq := Nat.mod_add_div v M
  have hv := Nat.mod_lt v hM
  have e : v + (M - v % M) = M * (v / M + 1) := by rw [Nat.mul_succ]; omega
  constructor
  · rw [Nat.mod_add_mod, Nat.add_assoc, e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hG]
  · rw [Nat.mod_add_mod, Nat.add_assoc, Nat.add_comm (M - v % M) v, e,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hG]

/-- Addition of `v` as a bijection. -/
def addBitsEquiv (b v : ℕ) : Qubits b ≃ Qubits b where
  toFun := addBits v
  invFun := addBits (2 ^ b - v % 2 ^ b)
  left_inv g := by
    simp only [addBits, bitsToNat_natToBits, Nat.mod_mod]
    rw [(addBits_arith _ _ v (Nat.two_pow_pos b) (bitsToNat_lt g)).1, natToBits_bitsToNat]
  right_inv g := by
    simp only [addBits, bitsToNat_natToBits, Nat.mod_mod]
    rw [(addBits_arith _ _ v (Nat.two_pow_pos b) (bitsToNat_lt g)).2, natToBits_bitsToNat]

/-- The phase-gradient state on `b` qubits. -/
noncomputable def gradVec (b : ℕ) (g : Qubits b) : ℂ :=
  ((Real.sqrt (2 ^ b) : ℂ))⁻¹ *
    Complex.exp (-(2 * Real.pi * Complex.I * (bitsToNat g : ℂ) / (2 ^ b : ℂ)))

/-- The phase `e^{2πi v/2^b}`. -/
noncomputable def kickPhase (b v : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / (2 ^ b : ℂ))







/-- Shear `(g, o) ↦ (g + v o, o)`. -/
def shearEquiv {O : Type*} (v : O → ℕ) : Qubits b × O ≃ Qubits b × O where
  toFun p := (addBitsEquiv b (v p.2) p.1, p.2)
  invFun p := ((addBitsEquiv b (v p.2)).symm p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- Add `v(rest)` into the register `w` (mod `2^b`). -/
noncomputable def kickEquiv (w : Fin b ↪ Fin N) (v : (Outside w → Bool) → ℕ) :
    Qubits N ≃ Qubits N :=
  (splitEquiv w).trans ((shearEquiv v).trans (splitEquiv w).symm)

/-- A state of the form `|gradient⟩_w ⊗ ψ(rest)`. -/
noncomputable def withGrad (w : Fin b ↪ Fin N) (ψ : (Outside w → Bool) → ℂ) : Qubits N → ℂ :=
  fun z => gradVec b (z ∘ w) * ψ (fun o => z o.1)



end OPI
end

-- ===== OPI.Arith =====
section

/-! # M3: register values and the controlled increment -/

namespace OPI

open QAlgorithms

variable {N : ℕ}

/-- Value of a register given as a list of wires, most significant first. -/
def regVal : List (Fin N) → Qubits N → ℕ
  | [], _ => 0
  | a :: r, z => (if z a then 2 ^ r.length else 0) + regVal r z









/-- Increment `r` (most significant first) by one, controlled on all of `cs`. -/
def incr (cs as : List (Fin N)) : List (Fin N) → List (RGate N)
  | [] => []
  | a :: r => mcx (cs ++ r) as a ++ incr cs as r



end OPI
end

-- ===== OPI.Adder =====
section

/-! # M3: adding a register into another (mod `2^b`) -/

namespace OPI

open QAlgorithms

variable {N : ℕ}







/-- Add `x` (register `xs`, most significant first) into `gs`. -/
def addInto (as : List (Fin N)) (gs : List (Fin N)) : List (Fin N) → List (RGate N)
  | [] => []
  | x :: xs => incr [x] as (gs.take (gs.length - xs.length)) ++ addInto as gs xs







end OPI
end

-- ===== OPI.KickCirc =====
section

/-! # M4: the kickback circuit (adder into the gradient register) -/

namespace OPI

open QAlgorithms Matrix

variable {N b : ℕ}

/-- A reversible circuit as a bijection. -/
def revEquiv (L : List (RGate N)) : Qubits N ≃ Qubits N where
  toFun := revAct L
  invFun := revAct L.reverse
  left_inv z := revAct_reverse L z
  right_inv z := revAct_reverse' L z

/-- Read a register from the outside of `w`. -/
def outVal (w : Fin b ↪ Fin N) (xs : List (Fin N)) (o : Outside w → Bool) : ℕ :=
  regVal xs (fun a => if h : a ∈ Set.range w then false else o ⟨a, h⟩)









/-- Clean-ancilla support of a state on the outside of `w`. -/
def CleanOn (w : Fin b ↪ Fin N) (as : List (Fin N)) (ψ : (Outside w → Bool) → ℂ) : Prop :=
  ∀ o, (∃ x ∈ as, ∃ h : x ∉ Set.range w, o ⟨x, h⟩ = true) → ψ o = 0



end OPI
end

-- ===== OPI.Lookup =====
section

/-! # M3: pattern tests and lookup tables -/

namespace OPI

open QAlgorithms

variable {N : ℕ}

/-- X gates on the wires of `xs` where the pattern bit is `false`. -/
def flipZeros : List (Fin N) → List Bool → List (RGate N)
  | x :: xs, b :: bs => (if b then [] else [.x x]) ++ flipZeros xs bs
  | _, _ => []

/-- Flip the wires `xs` where the pattern bit is `false`. -/
def applyFlips : List (Fin N) → List Bool → Qubits N → Qubits N
  | x :: xs, b :: bs, z => applyFlips xs bs (if b then z else Function.update z x (!z x))
  | _, _, z => z











/-- Flip `f` iff the register `xs` holds the pattern `bs`. -/
def eqFlip (xs : List (Fin N)) (bs : List Bool) (as : List (Fin N)) (f : Fin N) :
    List (RGate N) :=
  flipZeros xs bs ++ mcx xs as f ++ flipZeros xs bs



/-- XOR the constant `bs` into `ys`, controlled on `f`. -/
def cxOut (f : Fin N) : List (Fin N) → List Bool → List (RGate N)
  | y :: ys, b :: bs => (if b then [.cx f y] else []) ++ cxOut f ys bs
  | _, _ => []

/-- `ys ⊕= bs`. -/
def xorInto : List (Fin N) → List Bool → Qubits N → Qubits N
  | y :: ys, b :: bs, z => xorInto ys bs (if b then Function.update z y (!z y) else z)
  | _, _, z => z







/-- XOR of all table rows whose pattern equals `v`. -/
def xorAll (ys : List (Fin N)) : List (List Bool × List Bool) → List Bool → Qubits N → Qubits N
  | [], _, z => z
  | e :: T, v, z => xorAll ys T v (if v = e.1 then xorInto ys e.2 z else z)

/-- Table lookup: `ys ⊕= T[xs]`. -/
def lookup (xs ys as : List (Fin N)) (f : Fin N) :
    List (List Bool × List Bool) → List (RGate N)
  | [] => []
  | e :: T => eqFlip xs e.1 as f ++ cxOut f ys e.2 ++ eqFlip xs e.1 as f ++ lookup xs ys as f T



end OPI
end

-- ===== OPI.KickGen =====
section

/-! # M4: general kickback circuits and table-driven phases -/

namespace OPI

open QAlgorithms Matrix

variable {N b : ℕ}

/-- Clean configurations: all wires of `cl` are `false`. -/
def Clean (cl : List (Fin N)) (z : Qubits N) : Prop := ∀ a ∈ cl, z a = false



end OPI
end

-- ===== OPI.QFTDeWolf =====
section
set_option autoImplicit false

open QAlgorithms
open scoped Matrix BigOperators

/-! Ported from the accepted platform proof of `QAlgorithms.DeWolf.qft_circuit_exact`. -/
namespace SolQFTCircuitExact

/-- The single wire `q` as an embedding `Fin 1 ↪ Fin n`. -/
def wire1 {n : ℕ} (q : Fin n) : Fin 1 ↪ Fin n :=
  ⟨fun _ => q, fun a b _ => Subsingleton.elim a b⟩

/-- The wires `(c, t)`, `c ≠ t`, as an embedding `Fin 2 ↪ Fin n`. -/
def wire2 {n : ℕ} (c t : Fin n) (hct : c ≠ t) : Fin 2 ↪ Fin n :=
  ⟨Fin.cons c fun _ : Fin 1 => t,
    Fin.cons_injective_iff.2 ⟨by rintro ⟨_, h⟩; exact hct h.symm,
      fun a b _ => Subsingleton.elim a b⟩⟩

@[simp]
lemma init_snoc_qubits {n : ℕ} (u : Qubits n) (b : Bool) :
    Fin.init (Fin.snoc u b : Qubits (n + 1)) = u := by
  simp

@[simp]
lemma snoc_last_qubits {n : ℕ} (u : Qubits n) (b : Bool) :
    (Fin.snoc u b : Qubits (n + 1)) (Fin.last n) = b := by
  simp

@[simp]
lemma snoc_castSucc_qubits {n : ℕ} (u : Qubits n) (b : Bool) (i : Fin n) :
    (Fin.snoc u b : Qubits (n + 1)) (Fin.castSucc i) = u i := by
  simp

/-- Embed a circuit on `n` wires into `n + 1` wires on the first `n` wires `Fin.castSuccEmb`. -/
def liftGateApp {S : Set Gate} {n : ℕ} (g : GateApp S n) : GateApp S (n + 1) :=
  ⟨g.gate, g.mem, g.wires.trans Fin.castSuccEmb⟩

def liftCircuit {S : Set Gate} {n : ℕ} (c : Circuit S n) : Circuit S (n + 1) :=
  c.map liftGateApp

@[simp]
lemma liftCircuit_size {S : Set Gate} {n : ℕ} (c : Circuit S n) :
    Circuit.size (liftCircuit c) = Circuit.size c := by
  simp [Circuit.size, liftCircuit]

/-- Block-diagonal extension of an `n`-qubit operator to `n + 1` qubits acting on `Fin.init`. -/
def liftInit {n : ℕ} (A : Matrix (Qubits n) (Qubits n) ℂ) :
    Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ :=
  Matrix.of fun y z =>
    if y (Fin.last n) = z (Fin.last n) then A (Fin.init y) (Fin.init z) else 0

@[simp]
lemma liftInit_apply {n : ℕ} (A : Matrix (Qubits n) (Qubits n) ℂ) (y z : Qubits (n + 1)) :
    liftInit A y z = if y (Fin.last n) = z (Fin.last n) then A (Fin.init y) (Fin.init z) else 0 :=
  rfl















lemma circuit_size_append {S : Set Gate} {n : ℕ} (c1 c2 : Circuit S n) :
    Circuit.size (c1 ++ c2) = Circuit.size c1 + Circuit.size c2 := by
  simp [Circuit.size]



/-- Controlled-`R_s` gate application on wires `c ≠ t`. -/
noncomputable def ctrlRotApp {n : ℕ} (s : ℕ) (hs : 1 ≤ s) (c t : Fin n) (hct : c ≠ t) :
    GateApp qftGateSet n :=
  ⟨Gate.ofMatrix2 (controlled (rotR s)),
    Or.inl (Or.inr ⟨s, hs, rfl⟩),
    wire2 c t hct⟩



/-- Phase circuit of `n` controlled-`R_{m+2}` gates on `(castSucc m, last n)`. -/
noncomputable def phaseCircuit (n : ℕ) : Circuit qftGateSet (n + 1) :=
  List.ofFn fun m : Fin n =>
    ctrlRotApp ((m : ℕ) + 2) (by omega) (Fin.castSucc m) (Fin.last n) (Fin.castSucc_ne_last m)

@[simp]
lemma phaseCircuit_size (n : ℕ) : Circuit.size (phaseCircuit n) = n := by
  simp [Circuit.size, phaseCircuit]





/-- Hadamard gate application on wire `q`. -/
noncomputable def hadApp {n : ℕ} (q : Fin n) : GateApp qftGateSet n :=
  ⟨Gate.ofMatrix1 hadamard, Or.inl (Or.inl rfl), wire1 q⟩



/-- SWAP gate application on wires `c ≠ t`. -/
def swapApp {n : ℕ} (c t : Fin n) (hct : c ≠ t) : GateApp qftGateSet n :=
  ⟨Gate.ofMatrix2 swapGate, Or.inr rfl, wire2 c t hct⟩





/-- Sequence of `n` SWAP gates cycling `(0, 1, ..., n)`. -/
def cycleSwaps : (n : ℕ) → Circuit qftGateSet (n + 1)
  | 0 => []
  | m + 1 =>
      [swapApp (Fin.castSucc (Fin.last m)) (Fin.last (m + 1)) (Fin.castSucc_ne_last _)] ++
        liftCircuit (cycleSwaps m)

@[simp]
lemma cycleSwaps_size (n : ℕ) : Circuit.size (cycleSwaps n) = n := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [cycleSwaps, circuit_size_append, liftCircuit_size, ih]
      simp [Circuit.size]
      omega



















/-- Full QFT circuit on `n` qubits. -/
noncomputable def qftCircuit : (n : ℕ) → Circuit qftGateSet n
  | 0 => []
  | n + 1 =>
      liftCircuit (qftCircuit n) ++ phaseCircuit n ++ [hadApp (Fin.last n)] ++ cycleSwaps n







end SolQFTCircuitExact

end

-- ===== OPI.Cat =====
section

/-!
# M4: the catalytic layout

System wires `0, …, n-1`, gradient register on the last `b` wires. `Cat cl C U`: the circuit
`C` maps `ψ ⊗ |G_b⟩` to `(U ψ) ⊗ |G_b⟩` for every `ψ` vanishing unless the wires `cl` are clean.
-/

namespace OPI

open QAlgorithms Matrix

variable {n b : ℕ}

/-- System wires. -/
def sysEmb : Fin n ↪ Fin (n + b) := ⟨Fin.castAdd b, Fin.castAdd_injective n b⟩

/-- Gradient wires. -/
def gradEmb : Fin b ↪ Fin (n + b) := ⟨Fin.natAdd n, (Fin.natAddEmb n).injective⟩

/-- Split a configuration into system and gradient parts. -/
def appendEquiv (n b : ℕ) : Qubits n × Qubits b ≃ Qubits (n + b) where
  toFun p := Fin.append p.1 p.2
  invFun z := (z ∘ Fin.castAdd b, z ∘ Fin.natAdd n)
  left_inv p := by ext i <;> simp
  right_inv z := by funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- Product vector. -/
def tens (ψ : Qubits n → ℂ) (φ : Qubits b → ℂ) : Qubits (n + b) → ℂ :=
  fun z => ψ (z ∘ Fin.castAdd b) * φ (z ∘ Fin.natAdd n)



lemma castAdd_notMem_range_natAdd (i : Fin n) :
    Fin.castAdd b i ∉ Set.range (gradEmb (n := n) (b := b)) := by
  rintro ⟨j, hj⟩
  have h2 : n + (j : ℕ) = i := by
    have := congrArg Fin.val hj
    exact this
  have := i.isLt; omega





/-- `C` implements `U` on clean system states, leaving the gradient register intact. -/
def Cat (cl : List (Fin n)) (C : Circuit htcxGateSet (n + b)) (U : Mat n) : Prop :=
  ∀ ψ : Qubits n → ℂ, (∀ x, ψ x ≠ 0 → ∀ a ∈ cl, x a = false) →
    C.unitary.mulVec (tens ψ (gradVec b)) = tens (U.mulVec ψ) (gradVec b)

/-- `U` keeps clean states clean. -/
def PresClean (cl : List (Fin n)) (U : Mat n) : Prop :=
  ∀ ψ : Qubits n → ℂ, (∀ x, ψ x ≠ 0 → ∀ a ∈ cl, x a = false) →
    ∀ x, U.mulVec ψ x ≠ 0 → ∀ a ∈ cl, x a = false









/-! ### Kickback in the layout -/

/-- Read a system configuration from the outside of the gradient register. -/
def sysOf (o : Outside (gradEmb (n := n) (b := b)) → Bool) : Qubits n :=
  fun i => o ⟨Fin.castAdd b i, castAdd_notMem_range_natAdd i⟩





end OPI
end

-- ===== OPI.TablePhase =====
section

/-! # M4: table-driven phases `e^{2πi T[x]/2^b}` -/

namespace OPI

open QAlgorithms Matrix

variable {N : ℕ}

/-- The bit XORed into wire `a` by `xorInto ys bs`. -/
def xorBit : List (Fin N) → List Bool → Fin N → Bool
  | y :: ys, b :: bs, a => xor (decide (y = a) && b) (xorBit ys bs a)
  | _, _, _ => false



/-- The bit XORed into wire `a` by `xorAll ys T v`. -/
def xorAllBit (ys : List (Fin N)) : List (List Bool × List Bool) → List Bool → Fin N → Bool
  | [], _, _ => false
  | e :: T, v, a => xor (decide (v = e.1) && xorBit ys e.2 a) (xorAllBit ys T v a)







section Layout
variable {n b : ℕ}

/-- Value written by a table into a clean scratch register. -/
def tableNat (scr : List (Fin N)) (T : List (List Bool × List Bool)) (v : List Bool) : ℕ :=
  regVal scr (fun a => xorAllBit scr T v a)

/-- The table-phase circuit: look up into `scr`, add `scr` into the gradient, look up again. -/
def tablePhaseGates (xs scr as : List (Fin n)) (f : Fin n) (T : List (List Bool × List Bool)) :
    List (RGate (n + b)) :=
  let up := lookup (xs.map (Fin.castAdd b)) (scr.map (Fin.castAdd b)) (as.map (Fin.castAdd b))
    (Fin.castAdd b f) T
  up ++ addInto (as.map (Fin.castAdd b)) (List.ofFn (gradEmb (n := n) (b := b)))
    (scr.map (Fin.castAdd b)) ++ up







end Layout

end OPI
end

-- ===== OPI.QFT2 =====
section

/-! # M4: exact controlled rotations and QFT over `2^t` from the gradient -/

namespace OPI

open QAlgorithms Matrix

variable {N : ℕ}

/-- Binary value of a bit list, most significant first. -/
def bitsVal : List Bool → ℕ
  | [] => 0
  | x :: xs => (if x then 2 ^ xs.length else 0) + bitsVal xs



/-- `L`-bit binary expansion of `k mod 2^L`, most significant first. -/
def natBits (L k : ℕ) : List Bool := List.ofFn (natToBits L k)













end OPI

namespace OPI

open QAlgorithms Matrix SolQFTCircuitExact

variable {n b : ℕ}

/-- Workspace for catalysed gadgets: scratch, ancillas and a flag (system wires). -/
structure WS (n b : ℕ) where
  scr : List (Fin n)
  as : List (Fin n)
  f : Fin n
  hscr : scr.length = b
  has : 1 + b ≤ as.length + 2
  hnd : (scr ++ as ++ [f]).Nodup

/-- Clean wires of a workspace. -/
def WS.cl (W : WS n b) : List (Fin n) := W.scr ++ W.as ++ [W.f]





/-! ### Gadgets on system wires -/

/-- Hadamard. -/
noncomputable def hadGad (q : Fin n) : Circuit htcxGateSet (n + b) := [relocApp sysEmb (hApp q)]

/-- Controlled `R_s` via a table phase. -/
noncomputable def crGad (W : WS n b) (s : ℕ) (c t : Fin n) : Circuit htcxGateSet (n + b) :=
  revCirc (tablePhaseGates [c, t] W.scr W.as W.f [([true, true], natBits b (2 ^ (b - s)))])

/-- Swap by three CNOTs. -/
noncomputable def swGad (c t : Fin n) : Circuit htcxGateSet (n + b) :=
  relocCirc sysEmb (revCirc [.cx c t, .cx t c, .cx c t])












/-! ### Matching the gates of the ported QFT circuit -/












/-! ### The catalysed QFT circuit -/

/-- Gadgets for `phaseCircuit t` on the register `v`. -/
noncomputable def phaseGL (W : WS n b) (t : ℕ) (v : Fin (t + 1) → Fin n) :
    List (Circuit htcxGateSet (n + b)) :=
  List.ofFn fun m : Fin t => crGad W ((m : ℕ) + 2) (v (Fin.castSucc m)) (v (Fin.last t))

/-- Gadgets for `cycleSwaps m`. -/
noncomputable def swapsGL : (m : ℕ) → (Fin (m + 1) → Fin n) → List (Circuit htcxGateSet (n + b))
  | 0, _ => []
  | m + 1, v => [swGad (v (Fin.castSucc (Fin.last m))) (v (Fin.last (m + 1)))] ++
      swapsGL m (v ∘ Fin.castSucc)

/-- Gadgets for `qftCircuit t`. -/
noncomputable def qftGL (W : WS n b) : (t : ℕ) → (Fin t → Fin n) → List (Circuit htcxGateSet (n + b))
  | 0, _ => []
  | t + 1, v => qftGL W t (v ∘ Fin.castSucc) ++ phaseGL W t v ++ [hadGad (v (Fin.last t))] ++
      swapsGL t v

/-- The relation "gadget implements gate on register `v`". -/
def GRel {S : Set Gate} {t : ℕ} (cl : List (Fin n)) (v : Fin t ↪ Fin n) (g : GateApp S t)
    (C : Circuit htcxGateSet (n + b)) : Prop :=
  Cat cl C (embedOp g.gate.mat (g.wires.trans v)) ∧ PresClean cl (embedOp g.gate.mat (g.wires.trans v))

















end OPI
end

-- ===== OPI.Inverse =====
section

/-! # M2: inverse circuits (`T† = T^7`) -/

namespace OPI

open QAlgorithms Matrix

variable {N : ℕ}

open Classical in
/-- The inverse of one gate application: `T ↦ T^7`, `H, CNOT` self-inverse. -/
noncomputable def invApp (g : GateApp htcxGateSet N) : Circuit htcxGateSet N :=
  if g.gate = Gate.ofMatrix1 gateT then List.replicate 7 g else [g]

/-- The inverse circuit. -/
noncomputable def invCirc (C : Circuit htcxGateSet N) : Circuit htcxGateSet N :=
  C.reverse.flatMap invApp

















end OPI
end

-- ===== OPI.Pure =====
section

/-!
# M1: pure-state output laws

`lawP P f mem` is the output law from the (unnormalized) pure state `f`. Step equations,
scaling, and the bound `|lawP f − lawP g| ≤ ‖f − g‖ (‖f‖ + ‖g‖)`.
-/

namespace OPI

open QAlgorithms QAlgorithms.OPI Matrix

open scoped ComplexConjugate ComplexOrder

variable {N c out : ℕ}

/-- Rank-one density `|f⟩⟨f|`. -/
noncomputable def dens (f : Qubits N → ℂ) : Mat N := Matrix.of fun a b => f a * conj (f b)

/-- Squared norm. -/
noncomputable def nsq (f : Qubits N → ℂ) : ℝ := ∑ z, Complex.normSq (f z)

/-- Pure-state output law (oracle-free programs). -/
noncomputable def lawP (P : Prog N c out) (event : Option (Fin out → Bool) → Prop)
    (f : Qubits N → ℂ) (mem : Fin c → Bool) : ℝ :=
  lawFrom (fun k : Fin 0 => k.elim0) P event (dens f) mem













/-! ### Step equations -/





















end OPI

namespace OPI

open QAlgorithms QAlgorithms.OPI Matrix

open scoped ComplexConjugate ComplexOrder

variable {N c out : ℕ}







open Classical in
/-- Flattened Kraus list with event flags. -/
noncomputable def kList (P : Prog N c out) (event : Option (Fin out → Bool) → Prop)
    (mem : Fin c → Bool) : List (Bool × Mat N) :=
  (execKraus (fun k : Fin 0 => k.elim0) P mem).flatMap fun t =>
    t.2.1.map fun K => (decide (event t.1), K)















end OPI
end

-- ===== OPI.Perm =====
section

/-! # M3: function tables over all patterns, register swaps, in-place permutations -/

namespace OPI

open QAlgorithms

variable {N : ℕ}

/-- All bit lists of length `k`. -/
def allPats : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (allPats k).flatMap fun l => [false :: l, true :: l]





/-- The table of a function on all patterns of length `k`. -/
def funTable (k : ℕ) (F : List Bool → List Bool) : List (List Bool × List Bool) :=
  (allPats k).map fun p => (p, F p)





/-- Lookup of a total function: `ys ⊕= F(xs)`. -/
def lookupF (xs ys as : List (Fin N)) (f : Fin N) (F : List Bool → List Bool) : List (RGate N) :=
  lookup xs ys as f (funTable xs.length F)





end OPI

namespace OPI

open QAlgorithms

variable {N : ℕ}

/-- Overwrite register `r` with the bits `bs`. -/
def writeReg (r : List (Fin N)) (bs : List Bool) (z : Qubits N) : Qubits N :=
  fun a => if a ∈ r then bs.getD (r.idxOf a) false else z a











/-- Swap registers `B` and `Z` bitwise by three CNOTs per pair. -/
def swapRegs : List (Fin N) → List (Fin N) → List (RGate N)
  | b :: bs, w :: ws => [.cx b w, .cx w b, .cx b w] ++ swapRegs bs ws
  | _, _ => []





end OPI

namespace OPI

open QAlgorithms

variable {N : ℕ}

/-- In-place `B ← F(c, B)` (with inverse `Finv`), controls `cs`, clean scratch `Z`. -/
def permGad (cs B Z as : List (Fin N)) (f : Fin N) (F Finv : List Bool → List Bool → List Bool) :
    List (RGate N) :=
  lookupF (cs ++ B) Z as f (fun pat => F (pat.take cs.length) (pat.drop cs.length)) ++
  lookupF (cs ++ Z) B as f (fun pat => Finv (pat.take cs.length) (pat.drop cs.length)) ++
  swapRegs B Z





end OPI
end

-- ===== OPI.Tens =====
section

/-!
# Registers as tensor factors

For a register `w : Fin k ↪ Fin n`, a configuration splits into its `w`-part and its outside
part (`splitEquiv`). We use this to

* write the action of `embedOp M w` pointwise (`embedOp_mulVec_apply`),
* define "`w`-factorised" vectors `bfac w h g` (`h` on the register, `g` on the rest, read with the
  register cleared), and compute their inner products.
-/

namespace OPI

open QAlgorithms Matrix

variable {k n : ℕ}

/-- Assemble a configuration from a register value and an outside configuration. -/
noncomputable def joinE (w : Fin k ↪ Fin n) (y : Qubits k) (o : Outside w → Bool) : Qubits n :=
  (splitEquiv w).symm (y, o)

@[simp] lemma joinE_comp (w : Fin k ↪ Fin n) (y : Qubits k) (o : Outside w → Bool) :
    joinE w y o ∘ w = y := by
  have := congrArg Prod.fst ((splitEquiv w).apply_symm_apply (y, o))
  rwa [splitEquiv_fst] at this

lemma joinE_apply (w : Fin k ↪ Fin n) (y : Qubits k) (o : Outside w → Bool) (i : Fin k) :
    joinE w y o (w i) = y i := congrFun (joinE_comp w y o) i

lemma joinE_out (w : Fin k ↪ Fin n) (y : Qubits k) (o : Outside w → Bool) (a : Outside w) :
    joinE w y o a.1 = o a := by
  have := congrArg Prod.snd ((splitEquiv w).apply_symm_apply (y, o))
  rw [splitEquiv_snd] at this
  exact congrFun this a



/-- Overwrite the register `w` of `z` by `y`. -/
noncomputable def setE (w : Fin k ↪ Fin n) (z : Qubits n) (y : Qubits k) : Qubits n :=
  joinE w y (fun a => z a.1)

lemma setE_self (w : Fin k ↪ Fin n) (z : Qubits n) (y : Qubits k) (i : Fin k) :
    setE w z y (w i) = y i := joinE_apply w y _ i

lemma setE_out (w : Fin k ↪ Fin n) (z : Qubits n) (y : Qubits k) (a : Fin n)
    (ha : a ∉ Set.range w) : setE w z y a = z a := joinE_out w y _ ⟨a, ha⟩

@[simp] lemma setE_comp (w : Fin k ↪ Fin n) (z : Qubits n) (y : Qubits k) :
    setE w z y ∘ w = y := joinE_comp w y _

/-- Extensionality for configurations along a register. -/
lemma ext_reg (w : Fin k ↪ Fin n) {z z' : Qubits n} (h1 : ∀ i, z (w i) = z' (w i))
    (h2 : ∀ a, a ∉ Set.range w → z a = z' a) : z = z' := by
  funext a
  by_cases ha : a ∈ Set.range w
  · obtain ⟨i, rfl⟩ := ha; exact h1 i
  · exact h2 a ha

lemma setE_comp_self (w : Fin k ↪ Fin n) (z : Qubits n) : setE w z (z ∘ w) = z :=
  ext_reg w (fun i => by rw [setE_self]; rfl) (fun a ha => setE_out w z _ a ha)

lemma setE_setE (w : Fin k ↪ Fin n) (z : Qubits n) (y y' : Qubits k) :
    setE w (setE w z y) y' = setE w z y' :=
  ext_reg w (fun i => by rw [setE_self, setE_self])
    (fun a ha => by rw [setE_out _ _ _ _ ha, setE_out _ _ _ _ ha, setE_out _ _ _ _ ha])









/-- Clear the register `w`. -/
noncomputable def clrE (w : Fin k ↪ Fin n) (z : Qubits n) : Qubits n := setE w z (fun _ => false)



/-- A `w`-factorised vector: `h` on the register `w`, `g` on the rest (read with `w` cleared). -/
noncomputable def bfac (w : Fin k ↪ Fin n) (h : Qubits k → ℂ) (g : Qubits n → ℂ) :
    Qubits n → ℂ :=
  fun z => h (z ∘ w) * g (clrE w z)









end OPI
end

-- ===== OPI.SymEnc =====
section

/-!
# Symbol configurations on qubits

`m` coordinates, each a pair of symbols `(x_i, y_i) ∈ K × K` held in the registers
`S_i = reg (i, false, ·)` and `T_i = reg (i, true, ·)` of `L` qubits, with an injective encoding
`enc : K → Qubits L`. All other qubits are `0`.

* `cfg a`: the configuration of the symbol tuple `a`;
* `J F = Σ_a F(a) |cfg a⟩`: the embedding of symbol-level states;
* `J_perm`: a permutation of configurations that maps `cfg a` to `cfg (σ a)` acts as `σ` on
  symbol-level states.
-/

namespace OPI

namespace SymEnc

open QAlgorithms

variable {n m L : ℕ} {K : Type} [Fintype K] [DecidableEq K]
  (reg : Fin m × Bool × Fin L ↪ Fin n) (enc : K → Qubits L)

/-- The bit at a register position. -/
def bitOf (a : Fin m → K × K) (p : Fin m × Bool × Fin L) : Bool :=
  enc (if p.2.1 then (a p.1).2 else (a p.1).1) p.2.2

open Classical in
/-- The configuration of a symbol tuple. -/
noncomputable def cfg (a : Fin m → K × K) : Qubits n := fun q =>
  if h : ∃ p, reg p = q then bitOf enc a (Classical.choose h) else false





/-- The `S_i` register. -/
def sReg (i : Fin m) : Fin L ↪ Fin n :=
  ⟨fun j => reg (i, false, j), fun j j' h => by simpa using reg.injective h⟩
/-- The `T_i` register. -/
def tReg (i : Fin m) : Fin L ↪ Fin n :=
  ⟨fun j => reg (i, true, j), fun j j' h => by simpa using reg.injective h⟩








/-- The embedding of symbol-level states. -/
noncomputable def J (Fn : (Fin m → K × K) → ℂ) : Qubits n → ℂ :=
  fun z => ∑ a, if z = cfg reg enc a then Fn a else 0

variable {reg enc}













variable (reg enc)

/-! ## Symbol-level kernel operators -/

/-- A kernel acting on coordinate `i`. -/
noncomputable def opK (i : Fin m) (κ : K × K → K × K → ℂ) (Fn : (Fin m → K × K) → ℂ) :
    (Fin m → K × K) → ℂ :=
  fun b => ∑ z, κ (b i) z * Fn (Function.update b i z)

/-- Product states. -/
noncomputable def prodF (g : Fin m → K × K → ℂ) : (Fin m → K × K) → ℂ := fun b => ∏ j, g j (b j)



/-! ## One-register operators on qubits -/



/-- The register of component `c` of coordinate `i`. -/
def bReg (i : Fin m) (c : Bool) : Fin L ↪ Fin n :=
  ⟨fun j => reg (i, c, j), fun j j' h => by simpa using reg.injective h⟩

/-- Component `c` of a pair. -/
def comp (c : Bool) (w : K × K) : K := if c then w.2 else w.1

/-- Replace component `c` of a pair. -/
def setComp (c : Bool) (w : K × K) (x : K) : K × K := if c then (w.1, x) else (x, w.2)









end SymEnc

end OPI
end

-- ===== OPI.Rus =====
section

/-!
# M5: repeat-until-success preparation of uniform states

One attempt applies `H` to every wire of a register `xs`, XORs the membership bit
`[xs ∈ T]` into a flag with a lookup table, and measures the flag. On outcome `1` the flag is
uncomputed and the register holds exactly the uniform superposition over `T`; on outcome `0` the
register is reset and the attempt is repeated. After `R` attempts the remaining weight is sent to
`fail`.

This file first adds pure-state step equations for `prepare` and `coin`, and pointwise formulas
for one-qubit operators.
-/

namespace OPI

open QAlgorithms QAlgorithms.OPI Matrix

open scoped ComplexConjugate

variable {N c out : ℕ}

/-! ## Pointwise one-qubit operators -/







/-! ## Step equations for `prepare` and `coin` -/







/-! ## Hadamard layers -/

/-- Clear the wires of a register. -/
def clr (xs : List (Fin N)) (z : Qubits N) : Qubits N := fun a => if a ∈ xs then false else z a

@[simp] lemma clr_nil (z : Qubits N) : clr [] z = z := by funext a; simp [clr]





/-- The `H` layer on a register. -/
noncomputable def hLayer (xs : List (Fin N)) : Circuit htcxGateSet N := xs.map hApp



/-! ## Permutation circuits -/





/-! ## Resetting a register -/

/-- Reset every wire of a register. -/
def resets : List (Fin N) → Prog N c out → Prog N c out
  | [], P => P
  | q :: xs, P => .prepare q (resets xs P)

/-- All bit patterns of length `k`, summed. -/
noncomputable def patSum (k : ℕ) (A : List Bool → ℂ) : ℝ :=
  ((allPats k).map fun v => Complex.normSq (A v)).sum







/-! ## Repeat-until-success -/

section RUS

variable (xs : List (Fin N)) (fl f0 : Fin N) (as : List (Fin N)) (memT : List Bool → Bool)
  (dst : Fin c)

/-- The membership lookup `fl ⊕= [xs ∈ T]`. -/
def rusLook : List (RGate N) := lookupF xs [fl] as f0 (fun v => [memT v])

/-- `R` attempts, then `fail`. -/
noncomputable def rusProg : ℕ → Prog N c out → Prog N c out
  | 0, _ => .fail
  | R + 1, P =>
      (circSeg (hLayer xs ++ revCirc (rusLook xs fl f0 as memT))).prog
        (.measure fl dst fun b =>
          if b then (circSeg (revCirc (rusLook xs fl f0 as memT))).prog P
          else resets xs (rusProg R P))

/-- Ancillas of the lookup clean. -/
def AncClean (z : Qubits N) : Prop := (∀ a ∈ as, z a = false) ∧ z f0 = false

instance (f0 : Fin N) (as : List (Fin N)) : DecidablePred (AncClean f0 as) := fun _ => by
  unfold AncClean; infer_instance

/-- The register, the flag and the ancillas clean. -/
def RusClean (z : Qubits N) : Prop :=
  (∀ a ∈ xs, z a = false) ∧ z fl = false ∧ AncClean f0 as z

/-- One minus the success probability of an attempt. -/
noncomputable def rusFail : ℝ :=
  patSum xs.length (fun v => if memT v then 0 else ((Real.sqrt 2 : ℂ))⁻¹ ^ xs.length)

/-- The (unnormalized) state after a successful attempt. -/
noncomputable def rusOut (g : Qubits N → ℂ) : Qubits N → ℂ := fun y =>
  if memT (xs.map y) then ((Real.sqrt 2 : ℂ))⁻¹ ^ xs.length * g (clr xs y) else 0

variable (hnd : (xs ++ [fl] ++ as ++ [f0]).Nodup) (hlen : xs.length ≤ as.length + 2)







end RUS





section RUSState

variable (xs : List (Fin N)) (fl f0 : Fin N) (as : List (Fin N)) (memT : List Bool → Bool)
  (hnd : (xs ++ [fl] ++ as ++ [f0]).Nodup) (hlen : xs.length ≤ as.length + 2)
  (g : Qubits N → ℂ) (hg : ∀ z, ¬ RusClean xs fl f0 as z → g z = 0)












end RUSState

end OPI
end

-- ===== OPI.EGad =====
section

/-!
# The `E` gadget (Appendix A.3)

On registers `S`, `T` (one field symbol each), an ancilla `a` and pattern-test ancillas `as`:

  `X a; H a; CSWAP(a; S, T); a ⊕= [S = 0]`.

For a state `f` supported on `a = 0`, `T = 0`, `S ≠ 0` (and clean test ancillas), the circuit
outputs `(f − f ∘ swap_{S,T}) / √2`, i.e. `(|w⟩|0⟩ − |0⟩|w⟩)/√2`.

We first prove a generic rule for reversible circuits acting on states supported on "clean"
configurations.
-/

namespace OPI

open QAlgorithms Matrix

variable {N : ℕ}



/-! ## `H` on a wire where the state vanishes at `0` -/



/-! ## The gadget -/

section E

variable (S T Z as : List (Fin N)) (a f : Fin N)

/-- Swap the contents of `S` and `T`. -/
def swapST (z : Qubits N) : Qubits N := writeReg (S ++ T) (T.map z ++ S.map z) z

/-- The controlled-swap permutation: swap the halves of `B` when the control is `1`. -/
def cswF (n : ℕ) (c B : List Bool) : List Bool := if c = [true] then B.drop n ++ B.take n else B

/-- The gadget's reversible part after the `H`: controlled swap, then the zero test. -/
noncomputable def eCirc : Circuit htcxGateSet N :=
  revCirc [RGate.x a] ++ [hApp a] ++
    revCirc (permGad [a] (S ++ T) Z as f (cswF S.length) (cswF S.length)) ++
    revCirc (eqFlip S (List.replicate S.length false) as a)

variable (hnd : ([a] ++ (S ++ T) ++ Z ++ as ++ [f]).Nodup) (hST : S.length = T.length)
  (hZ : (S ++ T).length = Z.length) (hlen : 1 + (S ++ T).length ≤ as.length + 2)

/-- Clean scratch. -/
def EClean (z : Qubits N) : Prop := (∀ x ∈ as, z x = false) ∧ z f = false ∧ ∀ x ∈ Z, z x = false

instance : DecidablePred (EClean Z as f) := fun _ => by unfold EClean; infer_instance





















end E

end OPI
end

-- ===== OPI.QPE =====
section

/-!
# M4: phase estimation of a modular shift

The register `B` holds residues mod `p` (values `< p`, `w` bits). The shift `y ↦ y + k mod p`
(identity on invalid encodings) has the Fourier vectors `fvec x` as eigenvectors. Coherent phase
estimation (QFT, controlled shifts, QFT) on a `t`-qubit control register multiplies a factorised
state `x̂ ⊗ g` by the amplitude `qpeAmp x ℓ` on control value `ℓ`.
-/

namespace OPI

open QAlgorithms Matrix

variable {n : ℕ}

/-! ### Roots of unity -/

/-- `e^{2πi k/p}`. -/
noncomputable def ωp (p : ℕ) (k : ℤ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * k / p)













/-- The Fourier vector `x̂(y) = ω^{xy}/√p` on valid encodings `y < p`. -/
noncomputable def fvec (p w x : ℕ) (y : Qubits w) : ℂ :=
  if bitsToNat y < p then ωp p (x * bitsToNat y) / Real.sqrt p else 0

/-! ### Shifts of bit lists -/





/-- Shift a valid encoding by `k` mod `p` (invalid encodings are fixed). -/
def shiftL (p w k : ℕ) (y : List Bool) : List Bool :=
  if bitsVal y < p then natBits w ((bitsVal y + k) % p) else y









/-! ### Writing registers -/







/-! ### Controlled shifts -/

/-- Controlled shift: if the control bit is set, shift by `k`. -/
def csF (p w k : ℕ) (c y : List Bool) : List Bool := if c = [true] then shiftL p w k y else y



/-- A list of controlled shifts `(control, amount)`. -/
def csList (p w : ℕ) (Bl Z as : List (Fin n)) (f : Fin n) : List (Fin n × ℕ) → List (RGate n)
  | [] => []
  | ck :: L => permGad [ck.1] Bl Z as f (csF p w ck.2) (csF p w (p - ck.2 % p)) ++
      csList p w Bl Z as f L



/-- Shift of a register value (as bits). -/
def shiftQ (p w k : ℕ) (y : Qubits w) : Qubits w :=
  if bitsToNat y < p then natToBits w ((bitsToNat y + k) % p) else y











/-- The ctrl register as a list of controlled shifts by `2^(t-1-i)`. -/
def ctrlShifts {t : ℕ} (cE : Fin t ↪ Fin n) : List (Fin n × ℕ) :=
  List.ofFn fun i : Fin t => (cE i, 2 ^ (t - 1 - (i : ℕ)))



/-! ### The QFT on a register -/







/-! ### Controlled shifts on factorised states -/









/-! ### Phase estimation -/

/-- Amplitude of control value `a` after phase estimation of eigenphase `-x/p`. -/
noncomputable def qpeAmp (p t x : ℕ) (a : Qubits t) : ℂ :=
  ∑ y, qftQubits t a y * ωp p (-((x * bitsToNat y : ℕ) : ℤ)) * ((Real.sqrt (2 ^ t : ℕ) : ℂ))⁻¹

/-- The phase-estimation matrix: QFT, controlled shifts, QFT. -/
noncomputable def qpeMat (p w : ℕ) {t : ℕ} (bE : Fin w ↪ Fin n) (cE : Fin t ↪ Fin n)
    (Z as : List (Fin n)) (f : Fin n) : Mat n :=
  embedOp (qftQubits t) cE *
    phPerm (revEquiv (csList p w (List.ofFn bE) Z as f (ctrlShifts cE))) 0 *
      embedOp (qftQubits t) cE



end OPI
end

-- ===== OPI.DecJ =====
section

/-!
# The decoder gadgets on symbol-level states

* `eCirc_J`: the `E` gadget on the registers of coordinate `i` acts on `J F` as the kernel
  `(δ_w − δ_{swap w})/√2` on that coordinate.
-/

namespace OPI

namespace SymEnc

open QAlgorithms

variable {n m L : ℕ} {K : Type} [Fintype K] [DecidableEq K] [Zero K]
  {reg : Fin m × Bool × Fin L ↪ Fin n} {enc : K → Qubits L}



/-- Swap the two symbols of a pair. -/
def swapP (w : K × K) : K × K := (w.2, w.1)

/-- Swap the pair of coordinate `i`. -/
def swapAt (i : Fin m) : (Fin m → K × K) ≃ (Fin m → K × K) where
  toFun a := Function.update a i (swapP (a i))
  invFun a := Function.update a i (swapP (a i))
  left_inv a := by funext j; by_cases h : j = i <;> simp [h, swapP]
  right_inv a := by funext j; by_cases h : j = i <;> simp [h, swapP]

section E

variable (i : Fin m) (Z as : List (Fin n)) (a f : Fin n)

/-- The `E` gadget on coordinate `i`. -/
noncomputable def eGad : Circuit htcxGateSet n :=
  eCirc (List.ofFn (bReg reg i false)) (List.ofFn (bReg reg i true)) Z as a f

variable (hnd : ([a] ++ (List.ofFn (bReg reg i false) ++ List.ofFn (bReg reg i true)) ++ Z ++ as ++
    [f]).Nodup) (hZ : 2 * L = Z.length) (hlen : 1 + 2 * L ≤ as.length + 2)
  (hout : ∀ p, reg p ≠ a ∧ reg p ≠ f ∧ (∀ x ∈ Z, reg p ≠ x) ∧ ∀ x ∈ as, reg p ≠ x)



/-- The kernel of `E`. -/
noncomputable def kE (w z : K × K) : ℂ :=
  ((if z = w then 1 else 0) - (if z = swapP w then 1 else 0)) / Real.sqrt 2





end E

/-! ## Symbol permutations on one component -/

section P

variable (enc) in
open Classical in
/-- Apply `τ` to an encoded symbol (identity on non-encodings). -/
noncomputable def pFun (τ : K → K) (_c bits : List Bool) : List Bool :=
  if h : ∃ x, List.ofFn (enc x) = bits then List.ofFn (enc (τ (Classical.choose h))) else bits







/-- Apply `τ` to the first symbol of coordinate `i` (an involution when `τ` is). -/
def updFst (i : Fin m) (τ : K → K) (hτ : ∀ x, τ (τ x) = x) : (Fin m → K × K) ≃ (Fin m → K × K) where
  toFun b := Function.update b i (τ (b i).1, (b i).2)
  invFun b := Function.update b i (τ (b i).1, (b i).2)
  left_inv b := by funext j; by_cases h : j = i <;> simp [h, hτ]
  right_inv b := by funext j; by_cases h : j = i <;> simp [h, hτ]

variable (i : Fin m) (Z as : List (Fin n)) (f : Fin n)

variable (reg enc) in
/-- The gadget applying `τ` to `S_i`. -/
noncomputable def pGad (τ : K → K) : List (RGate n) :=
  permGad [] (List.ofFn (bReg reg i false)) Z as f (pFun enc τ) (pFun enc τ)

variable (hnd : ([] ++ List.ofFn (bReg reg i false) ++ Z ++ as ++ [f]).Nodup) (hZ : L = Z.length)
  (hlen : L ≤ as.length + 2)
  (hout : ∀ p, reg p ≠ f ∧ (∀ x ∈ Z, reg p ≠ x) ∧ ∀ x ∈ as, reg p ≠ x)





end P

end SymEnc

end OPI
end

-- ===== OPI.Readout =====
section

/-!
# M4: reading out a phase-estimation register and subtracting the estimate

The accumulator `ac = top ++ lh :: lrest` (`t = |lrest| + 1` low bits) is set to
`2^(t-1) + p·ℓ`, where `ℓ` is the control value; its top part is `⌊(p ℓ + 2^(t-1))/2^t⌋`, the
rounded estimate of `p ℓ / 2^t`. The estimate (mod `p`) is subtracted from the register `A`, and
the accumulator is uncomputed.
-/

namespace OPI

open QAlgorithms Matrix

variable {n : ℕ}





/-- The readout circuit: set `lh`, then add the control register `p` times. -/
def rdList (p : ℕ) (ctrlL top : List (Fin n)) (lh : Fin n) (lrest as : List (Fin n)) :
    List (RGate n) :=
  RGate.x lh :: (List.replicate p (addInto as (top ++ lh :: lrest) ctrlL)).flatten





/-- The subtraction table: `y ← y - (c mod p)`. -/
def subF (p w : ℕ) (c y : List Bool) : List Bool := shiftL p w (p - bitsVal c % p) y

/-- The addition table: `y ← y + (c mod p)`. -/
def addF (p w : ℕ) (c y : List Bool) : List Bool := shiftL p w (bitsVal c % p) y

/-- Readout, subtraction, uncomputation. -/
def tauList (p w : ℕ) (ctrlL top : List (Fin n)) (lh : Fin n) (lrest Al Z as : List (Fin n))
    (f : Fin n) : List (RGate n) :=
  rdList p ctrlL top lh lrest as ++ permGad top Al Z as f (subF p w) (addF p w) ++
    (rdList p ctrlL top lh lrest as).reverse

/-- The rounded estimate. -/
def rdv (p t ℓ : ℕ) : ℕ := ((2 ^ (t - 1) + p * ℓ) / 2 ^ t) % p



end OPI
end

-- ===== OPI.VecNorm =====
section

/-!
# Norms of state vectors

`vnorm f = √(nsq f)` (Euclidean norm), unitary invariance, Pythagoras for orthogonal families, and
orthonormality of the Fourier vectors `fvec`.
-/

namespace OPI

open QAlgorithms Matrix

variable {n : ℕ}

/-- Euclidean norm of a state vector. -/
noncomputable def vnorm (f : Qubits n → ℂ) : ℝ :=
  ‖(WithLp.toLp 2 f : EuclideanSpace ℂ (Qubits n))‖

























/-! ### Orthonormality of Fourier vectors -/













end OPI
end

-- ===== OPI.QFTpMain =====
section

/-!
# M4: the `QFT_p` gadget, error analysis at the system level
-/

namespace OPI

open QAlgorithms Matrix

variable {n : ℕ}

/-- Layout of the `QFT_p` gadget on the system wires. -/
structure QLay (n p w t : ℕ) where
  aE : Fin w ↪ Fin n
  bE : Fin w ↪ Fin n
  cE : Fin t ↪ Fin n
  top : List (Fin n)
  lh : Fin n
  lrest : List (Fin n)
  Z : List (Fin n)
  as : List (Fin n)
  f : Fin n
  htop : top.length = w + 1
  hlrest : lrest.length + 1 = t
  hZ : Z.length = w
  has : t + 2 * w + 2 ≤ as.length
  hnd : (List.ofFn cE ++ (top ++ lh :: lrest) ++ List.ofFn aE ++ List.ofFn bE ++ Z ++ as ++
    [f]).Nodup

/-- The QFT matrix on residues `< p` (zero on invalid encodings). -/
noncomputable def qftP (p w : ℕ) : Matrix (Qubits w) (Qubits w) ℂ :=
  Matrix.of fun a y =>
    if bitsToNat a < p ∧ bitsToNat y < p then ωp p (bitsToNat a * bitsToNat y) / Real.sqrt p else 0

/-- Mass of the phase-estimation amplitudes on wrong estimates. -/
noncomputable def badMass (p t x : ℕ) : ℝ :=
  ∑ a : Qubits t, if rdv p t (bitsToNat a) ≠ x then Complex.normSq (qpeAmp p t x a) else 0

namespace QLay

variable {p w t : ℕ} (L : QLay n p w t)

/-- The accumulator. -/
def acc : List (Fin n) := L.top ++ L.lh :: L.lrest
/-- Lookup scratch. -/
def cl : List (Fin n) := L.Z ++ L.as ++ [L.f]
/-- Clean set: accumulator and scratch clean. -/
def C (z : Qubits n) : Prop := (∀ a ∈ L.acc, z a = false) ∧ ∀ a ∈ L.cl, z a = false

/-- Readout–subtract–uncompute. -/
def tauL : List (RGate n) :=
  tauList p w (List.ofFn L.cE) L.top L.lh L.lrest (List.ofFn L.aE) L.Z L.as L.f
/-- Final swap of `A` and `B`. -/
def swL : List (RGate n) := swapRegs (List.ofFn L.aE) (List.ofFn L.bE)

noncomputable def Qm : Mat n := qpeMat p w L.bE L.cE L.Z L.as L.f
noncomputable def tauM : Mat n := phPerm (revEquiv L.tauL) 0
noncomputable def swM : Mat n := phPerm (revEquiv L.swL) 0
noncomputable def Dideal : Mat n :=
  Matrix.diagonal fun z => ωp p (bitsToNat (z ∘ L.aE) * bitsToNat (z ∘ L.bE))

/-- Domain of the gadget: `B`, control register, accumulator and scratch clean; `A < p`. -/
def Dom (g : Qubits n → ℂ) : Prop :=
  ∀ z, g z ≠ 0 → z ∘ L.bE = (fun _ => false) ∧ z ∘ L.cE = (fun _ => false) ∧ L.C z ∧
    bitsToNat (z ∘ L.aE) < p

/-! ### Disjointness facts -/




























/-! ### The readout permutation on clean configurations -/







/-! ### The swap -/



/-! ### The pieces of the analysis -/

/-- The part of `g` with `A = x`. -/
noncomputable def gx (g : Qubits n → ℂ) (x : ℕ) : Qubits n → ℂ :=
  fun z => if bitsToNat (z ∘ L.aE) = x then g z else 0

/-- The part of `g` with `A = x`, moved to `A = 0`. -/
noncomputable def g0 (g : Qubits n → ℂ) (x : ℕ) : Qubits n → ℂ :=
  fun z => if bitsToNat (z ∘ L.aE) = 0 then L.gx g x (setE L.aE z (natToBits w x)) else 0













































end QLay

end OPI
end

-- ===== OPI.QFTpCirc =====
section

/-!
# M4: the `QFT_p` gadget as an `{H, T, CNOT}` circuit

The circuit (phase table, phase estimation, readout, inverse phase estimation, swap) is catalysed
by the gradient register and implements, on `|x⟩_A |u_p⟩_B`, the QFT over `ℤ_p` on `A` (with `B`
cleared) up to `2π/2^b + 2p/√(2^t)`.
-/

namespace OPI

open QAlgorithms Matrix

variable {n b : ℕ}

/-! ### Tables of total functions in a phase -/





/-- The phase table `(a, y) ↦ ⌊2^b ((a·y) mod p)/p⌋` on `w + w` bits. -/
def phaseTab (p w b : ℕ) : List (List Bool × List Bool) :=
  funTable (w + w) fun pat =>
    natBits b (2 ^ b * ((bitsVal (pat.take w) * bitsVal (pat.drop w)) % p) / p)







/-! ### The gadget -/

/-- Gadget data: the layout plus a gradient workspace. -/
structure QG (n b p w t : ℕ) extends QLay n p w t where
  W : WS n b
  hWa : ∀ i, aE i ∉ W.cl
  hWb : ∀ i, bE i ∉ W.cl
  hWc : ∀ i, cE i ∉ W.cl
  hWacc : ∀ a ∈ top ++ lh :: lrest, a ∉ W.cl
  htb : t ≤ b
  hwas : w + w ≤ W.as.length + 2

namespace QG

variable {p w t : ℕ} (G : QG n b p w t)

/-- All wires that are clean between the steps of the gadget. -/
def clG : List (Fin n) := G.W.cl ++ G.acc ++ G.cl

/-- Control register list. -/
def csL : List (RGate n) := csList p w (List.ofFn G.bE) G.Z G.as G.f (ctrlShifts G.cE)

noncomputable def phaseC : Circuit htcxGateSet (n + b) :=
  revCirc (tablePhaseGates (List.ofFn G.aE ++ List.ofFn G.bE) G.W.scr G.W.as G.W.f (phaseTab p w b))

noncomputable def qpeC : Circuit htcxGateSet (n + b) :=
  (qftGL G.W t G.cE).flatten ++ relocCirc sysEmb (revCirc G.csL) ++ (qftGL G.W t G.cE).flatten

/-- **The `QFT_p` gadget.** -/
noncomputable def circ : Circuit htcxGateSet (n + b) :=
  G.phaseC ++ G.qpeC ++ relocCirc sysEmb (revCirc G.tauL) ++ invCirc G.qpeC ++
    relocCirc sysEmb (revCirc G.swL)

noncomputable def Dreal : Mat n :=
  Matrix.diagonal fun x => kickPhase b (tableNat (G.W.scr.map (Fin.castAdd b)) (phaseTab p w b)
    ((List.ofFn G.aE ++ List.ofFn G.bE).map x))

noncomputable def Uq : Mat n := G.swM * (G.Qmᴴ * (G.tauM * (G.Qm * G.Dreal)))

































end QG

end OPI
end

-- ===== OPI.QFTBlocks =====
section

/-!
# M4: several `QFT_p` gadgets in sequence

A list of `QFT_p` gadgets (on disjoint `A`/`B` blocks, sharing the clean wires) applied one after
the other to `|u_p⟩^{⊗k} ⊗ g` implements the product of the ideal `QFT_p`'s up to `k` times the
single-gadget error. Also: the ideal `QFT_p` preserves norms on valid inputs.
-/

namespace OPI

open QAlgorithms Matrix

variable {n b : ℕ}

/-! ### The ideal `QFT_p` is an isometry on valid inputs -/











/-! ### Sequences of gadgets -/

namespace QG

variable {p w t : ℕ}

/-- Put `|u_p⟩` into every `B` register of the list. -/
noncomputable def prepAll : List (QG n b p w t) → (Qubits n → ℂ) → Qubits n → ℂ
  | [], g => g
  | G :: Gs, g => bfac G.bE (fvec p w 0) (prepAll Gs g)

/-- The ideal maps, head first. -/
noncomputable def idealAll : List (QG n b p w t) → (Qubits n → ℂ) → Qubits n → ℂ
  | [], g => g
  | G :: Gs, g => idealAll Gs ((embedOp (qftP p w) G.aE).mulVec g)

/-- The implemented system unitaries, head first. -/
noncomputable def UAll : List (QG n b p w t) → Mat n
  | [] => 1
  | G :: Gs => UAll Gs * G.Uq

/-- The circuits, head first. -/
noncomputable def circAll : List (QG n b p w t) → Circuit htcxGateSet (n + b)
  | [] => []
  | G :: Gs => G.circ ++ circAll Gs

/-- The wires a gadget needs clean or valid. -/
def wiresOf (G : QG n b p w t) (a : Fin n) : Prop :=
  a ∈ Set.range G.aE ∨ a ∈ Set.range G.bE ∨ a ∈ Set.range G.cE ∨ a ∈ G.acc ∨ a ∈ G.cl

/-- Register `v` avoids the wires of `G`. -/
def Avoids {k : ℕ} (v : Fin k ↪ Fin n) (G : QG n b p w t) : Prop := ∀ i, ¬ G.wiresOf (v i)

/-- Cross conditions between two different gadgets of the list. -/
def Cross (G G' : QG n b p w t) : Prop :=
  Avoids G.aE G' ∧ Avoids G.bE G' ∧ Avoids G'.aE G ∧ Avoids G'.bE G









/-- Domain of a whole list. -/
def AllDom : List (QG n b p w t) → (Qubits n → ℂ) → Prop
  | [], _ => True
  | G :: Gs, g => G.Dom g ∧ AllDom Gs g























end QG

end OPI
end

-- ===== OPI.Fq =====
section

/-!
# The field layer: trace, additive character, encodings

For a field presentation `F` (`K = F_p[X]/(f)`, `e = deg f`, `w = ⌈log₂ p⌉`):

* `tr = Tr_{K/F_p}`, the additive character `ψ(a) = ω^{tr a}`, character sums;
* trace-dual coordinates `sco x j = tr (x · X^j)` and `tr (x y) = Σ_j c_j(y) sco x j`;
* the encoding `enc = elemBits` (blocks of power-basis coordinates) and its inverse `dec`.
-/

namespace OPI

namespace Fq

open QAlgorithms TwoFoldOPI

variable (F : AvgCaseTI.FieldPres)

instance instModFinite : Module.Finite (ZMod F.p) F.F :=
  PowerBasis.finite (AdjoinRoot.powerBasis F.hirr.ne_zero)

/-- Number of power-basis coordinates. -/
abbrev e : ℕ := F.f.natDegree
/-- Bits per coordinate. -/
abbrev w : ℕ := Nat.clog 2 F.p

/-- The power basis. -/
noncomputable abbrev bas : Module.Basis (Fin F.f.natDegree) (ZMod F.p) F.F := (fieldBasis F).basis


lemma p_le : F.p ≤ 2 ^ w F := Nat.le_pow_clog one_lt_two _


/-- The trace to `F_p`. -/
noncomputable def tr (x : F.F) : ZMod F.p := Algebra.trace (ZMod F.p) F.F x

/-- The additive character `ψ(a) = e^{2πi tr(a)/p}`. -/
noncomputable def ψ (x : F.F) : ℂ := ωp F.p (tr F x).val













/-! ### Trace-dual coordinates -/

/-- `sco x j = tr (x · X^j)`. -/
noncomputable def sco (x : F.F) (j : Fin F.f.natDegree) : ZMod F.p := tr F (x * bas F j)





/-! ### Encodings -/



/-- Decoding inverts encoding. -/
lemma decode_elemBits (x : F.F) : decodeElem F (elemBits F x) = x := by
  unfold decodeElem elemBits
  conv_rhs => rw [← (bas F).equivFun.symm_apply_apply x]
  congr 1
  funext j
  simp only [Equiv.symm_apply_apply, Module.Basis.equivFun_apply]
  rw [bitsToNat_natToBits, Nat.mod_eq_of_lt (lt_of_lt_of_le (ZMod.val_lt _) (p_le F)),
    ZMod.natCast_zmod_val]
  rfl



/-- Block `j` of a symbol. -/
def blk (j : Fin F.f.natDegree) : Fin (w F) ↪ Fin (bitsPerSymbol F) :=
  ⟨fun k => finProdFinEquiv (j, k), fun a b h => (Prod.ext_iff.mp (finProdFinEquiv.injective h)).2⟩





end Fq

end OPI
end

-- ===== OPI.GE =====
section

/-!
# M6: oblivious Gauss–Jordan elimination

Column-by-column elimination with one-hot pivot selection (no row swaps), as used by the
reversible decoder. Each column step selects the first unused row with a nonzero entry, normalises
it, and eliminates the column from all other rows. If the system `A z = b` (augmented matrix,
last column `b`) is solvable, the particular solution read off from the pivots solves it.
-/

namespace OPI

namespace GE

variable {K : Type*} [Field K] [DecidableEq K] {r c : ℕ}

/-- Augmented matrices: column `Fin.last c` is the right-hand side. -/
abbrev Aug (K : Type*) (r c : ℕ) := Fin r → Fin (c + 1) → K

/-- Candidate rows: nonzero entry in the column and not used yet. -/
def nz (A : Aug K r c) (u : Fin r → Bool) (col : Fin (c + 1)) (i : Fin r) : Prop :=
  A i col ≠ 0 ∧ u i = false

instance (A : Aug K r c) (u : Fin r → Bool) (col : Fin (c + 1)) (i : Fin r) :
    Decidable (nz A u col i) := by unfold nz; infer_instance

/-- One-hot selection of the first candidate row. -/
def sel (A : Aug K r c) (u : Fin r → Bool) (col : Fin (c + 1)) (i : Fin r) : Prop :=
  nz A u col i ∧ ∀ i' : Fin r, i' < i → ¬ nz A u col i'

instance (A : Aug K r c) (u : Fin r → Bool) (col : Fin (c + 1)) (i : Fin r) :
    Decidable (sel A u col i) := by unfold sel; infer_instance

/-- The selected row (zero if none). -/
def pivv (A : Aug K r c) (u : Fin r → Bool) (col : Fin (c + 1)) (k : Fin (c + 1)) : K :=
  ∑ i, if sel A u col i then A i k else 0

/-- The normalised selected row. -/
def pn (A : Aug K r c) (u : Fin r → Bool) (col : Fin (c + 1)) (k : Fin (c + 1)) : K :=
  (pivv A u col col)⁻¹ * pivv A u col k

/-- One elimination step. -/
def stepA (A : Aug K r c) (u : Fin r → Bool) (col : Fin (c + 1)) : Aug K r c :=
  fun i k => if sel A u col i then pn A u col k else A i k - A i col * pn A u col k

def stepU (A : Aug K r c) (u : Fin r → Bool) (col : Fin (c + 1)) : Fin r → Bool :=
  fun i => u i || decide (sel A u col i)

/-- State after processing the first `j` columns. -/
def run (A0 : Aug K r c) : ℕ → Aug K r c × (Fin r → Bool)
  | 0 => (A0, fun _ => false)
  | j + 1 =>
    if h : j < c then
      (stepA (run A0 j).1 (run A0 j).2 ⟨j, by omega⟩, stepU (run A0 j).1 (run A0 j).2 ⟨j, by omega⟩)
    else run A0 j

/-- Selection at column `j` (taken in the state before it). -/
def hist (A0 : Aug K r c) (j : Fin c) (i : Fin r) : Prop :=
  sel (run A0 j).1 (run A0 j).2 j.castSucc i

instance (A0 : Aug K r c) (j : Fin c) (i : Fin r) : Decidable (hist A0 j i) := by
  unfold hist; infer_instance

/-- The particular solution: pivot variables from the right-hand side, free variables `0`. -/
def solution (A0 : Aug K r c) (j : Fin c) : K :=
  ∑ i, if hist A0 j i then (run A0 c).1 i (Fin.last c) else 0

/-- `z` solves the system `A`. -/
def Solves (A : Aug K r c) (z : Fin c → K) : Prop :=
  ∀ i, ∑ k : Fin c, A i k.castSucc * z k = A i (Fin.last c)

/-! ### Basic facts on selection -/













/-! ### Residuals and equivalence of systems -/

/-- Residual of a row at `z`. -/
def resRow (R : Fin (c + 1) → K) (z : Fin c → K) : K :=
  ∑ k : Fin c, R k.castSucc * z k - R (Fin.last c)









/-! ### The invariant -/

/-- Invariant after `j` columns. -/
def Inv (A0 : Aug K r c) (j : ℕ) : Prop :=
  (∀ z, Solves A0 z ↔ Solves (run A0 j).1 z) ∧
  (∀ col : Fin c, col.val < j →
    (∀ p, hist A0 col p → (run A0 j).2 p = true ∧
      ∀ i, (run A0 j).1 i col.castSucc = if i = p then 1 else 0) ∧
    ((∀ i, ¬ hist A0 col i) → ∀ i, (run A0 j).2 i = false → (run A0 j).1 i col.castSucc = 0)) ∧
  (∀ i, (run A0 j).2 i = true → ∃ col : Fin c, col.val < j ∧ hist A0 col i)















end GE

end OPI
end

-- ===== OPI.Relin =====
section

/-!
# M6: the relinearization decoder

Given `s = c + c'` and `t = c c'` (coordinatewise), the decoder solves the relinearized system

  `w − s ∘ v + t = 0`,  `v ∈ D`, `w ∈ D^{*2}`

by oblivious Gauss–Jordan elimination in the coefficients of spanning families of `D` and
`D^{*2}`, and returns `v`. If the system has no solution with `v ≠ c`, the decoder returns `c`.
Hence, by `TwoFoldOPI.relin_unique_solution_bound`, it fails for at most `E (q−1)^m` of the
`c'` with `c'_i ≠ c_i` for all `i`.
-/

namespace OPI

namespace Relin

open TwoFoldOPI

variable {K : Type*} [Field K] [DecidableEq K] {m k k2 : ℕ}
  (bD : Fin k → Fin m → K) (bW : Fin k2 → Fin m → K)

/-- Row `i` of the coefficient matrix: unknowns `α` (for `v`) then `γ` (for `w`). -/
def coeffRow (s : Fin m → K) (i : Fin m) : Fin (k + k2) → K :=
  Fin.addCases (fun j => -(s i * bD j i)) (fun l => bW l i)

/-- The augmented matrix of the relinearized system. -/
def aug (s t : Fin m → K) : GE.Aug K m (k + k2) :=
  fun i => Fin.lastCases (-(t i)) (coeffRow bD bW s i)

/-- The decoded word. -/
def decode (s t : Fin m → K) : Fin m → K :=
  ∑ j : Fin k, GE.solution (aug bD bW s t) (Fin.castAdd k2 j) • bD j

/-- The `v`-part of an unknown vector. -/
def vOf (z : Fin (k + k2) → K) : Fin m → K := ∑ j : Fin k, z (Fin.castAdd k2 j) • bD j

/-- The `w`-part of an unknown vector. -/
def wOf (z : Fin (k + k2) → K) : Fin m → K := ∑ l : Fin k2, z (Fin.natAdd k l) • bW l



variable {D : Submodule K (Fin m → K)}









end Relin

end OPI
end

-- ===== OPI.DecProb =====
section

/-!
# Decoding probability of the ideal coordinate states

Measuring `|ψ_c⟩ = (2(q−1))^{-1/2} Σ_a (|c,a⟩ − |a,c⟩)` gives the ordered pair `(c, a)` or `(a, c)`
with `a ≠ c`, each with probability `1/(2(q−1))`. The symmetric functions `x + y = c + a` and
`xy = ca` do not see the order. Hence, for any test `H` of `(s, t)`,

  `Σ_{x,y} Π_i w_{d_i}(x_i, y_i) H(x+y, xy) = Σ_{c'} Π_i [c'_i ≠ d_i]/(q−1) · H(d+c', d c')`.

With `H = [decode = d]` and the failure count of `Relin.decode_fail_card`, the decoding probability
is at least `1 − E`.
-/

namespace OPI

namespace DecProb

open TwoFoldOPI

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {m : ℕ}

/-- Measurement weight of an ordered pair under `|ψ_c⟩`. -/
noncomputable def wPair (c : K) (p : K × K) : ℝ :=
  if (p.1 = c ∧ p.2 ≠ c) ∨ (p.2 = c ∧ p.1 ≠ c) then 1 / (2 * ((Fintype.card K : ℝ) - 1)) else 0

/-- The partner of `c` in a pair. -/
def partner (c : K) (p : K × K) : K := if p.1 = c then p.2 else p.1













end DecProb

end OPI
end

-- ===== OPI.CoordSym =====
section

/-!
# The coordinate gadget on symbols (Appendix A.3)

On functions `K → ℂ` (one field symbol) and `K × K → ℂ` (two symbols):

* `|A_β⟩ = (q−1)^{-1/2} Σ_{y ≠ β} |y⟩`, `Z^c|y⟩ = ψ(cy)|y⟩`, `P_β|y⟩ = |β − y⟩`;
* `E(f ⊗ δ_0) = (f ⊗ δ_0 − δ_0 ⊗ f)/√2`;
* `Q₂` is `QFT_q ⊗ QFT_q`.

Then `Q₂ E P_β Z^c |A_β⟩ = ψ(cβ) (2(q−1))^{-1/2} ([a₁ = c] − [a₂ = c])`, whose squared modulus is
the measurement weight `DecProb.wPair c`.
-/

namespace OPI

namespace CoordSym

open QAlgorithms

variable (F : AvgCaseTI.FieldPres)

local notation "q" => (Fintype.card F.F : ℝ)

/-- `|A_β⟩`. -/
noncomputable def aState (β : F.F) : F.F → ℂ := fun y => if y ≠ β then ((Real.sqrt (q - 1) : ℂ))⁻¹ else 0

/-- `Z^c`. -/
noncomputable def zOp (c : F.F) (f : F.F → ℂ) : F.F → ℂ := fun y => Fq.ψ F (c * y) * f y

/-- `P_β : |y⟩ ↦ |β − y⟩`. -/
noncomputable def pOp (β : F.F) (f : F.F → ℂ) : F.F → ℂ := fun z => f (β - z)

/-- `E` on a two-symbol state whose second symbol is `0`. -/
noncomputable def eOp (f : F.F → ℂ) : F.F × F.F → ℂ := fun z =>
  ((if z.2 = 0 then f z.1 else 0) - (if z.1 = 0 then f z.2 else 0)) / Real.sqrt 2

/-- `QFT_q ⊗ QFT_q`. -/
noncomputable def q2 (g : F.F × F.F → ℂ) : F.F × F.F → ℂ := fun a =>
  (∑ x : F.F × F.F, Fq.ψ F (a.1 * x.1 + a.2 * x.2) * g x) / q

/-- The ideal output `ψ(cβ) (2(q−1))^{-1/2} ([a₁ = c] − [a₂ = c])`. -/
noncomputable def psiState (β c : F.F) : F.F × F.F → ℂ := fun a =>
  Fq.ψ F (c * β) * (((if a.1 = c then 1 else 0) - (if a.2 = c then 1 else 0)) /
    Real.sqrt (2 * (q - 1)))















end CoordSym

end OPI
end

-- ===== OPI.QFTq =====
section

/-!
# M4: the QFT over `F_q`

`QFT_q |x⟩ = q^{-1/2} Σ_y ψ(x y) |y⟩` is implemented as the re-encoding `x ↦ (tr (x X^j))_j`
(a reversible permutation of valid encodings) followed by `QFT_p` on each of the `e` blocks:
`tr (x y) = Σ_j c_j(y) tr (x X^j)`.
-/

namespace OPI

open QAlgorithms TwoFoldOPI Matrix

namespace Fq

variable (F : AvgCaseTI.FieldPres)





/-- Encoding by trace-dual coordinates. -/
noncomputable def encS (x : F.F) : Qubits (bitsPerSymbol F) :=
  fun i => natToBits (w F) (sco F x (finProdFinEquiv.symm i).1).val (finProdFinEquiv.symm i).2



/-- Valid symbols: every block holds a residue `< p`. -/
def Valid (z : Qubits (bitsPerSymbol F)) : Prop := ∀ j, bitsToNat (z ∘ blk F j) < F.p








/-- The blocks of a valid symbol as residues. -/
noncomputable def blkVal (z : Qubits (bitsPerSymbol F)) (j : Fin F.f.natDegree) : ZMod F.p :=
  (bitsToNat (z ∘ blk F j) : ZMod F.p)









/-- The re-encoding on symbols: `elemBits x ↦ encS x`, identity on invalid symbols. -/
noncomputable def Rf (z : Qubits (bitsPerSymbol F)) : Qubits (bitsPerSymbol F) :=
  if h : ∃ x, elemBits F x = z then encS F (Classical.choose h) else z

/-- Its inverse. -/
noncomputable def Rinv (z : Qubits (bitsPerSymbol F)) : Qubits (bitsPerSymbol F) :=
  if h : ∃ x, encS F x = z then elemBits F (Classical.choose h) else z









/-- List versions (for `permGad`). -/
noncomputable def RL (_c y : List Bool) : List Bool :=
  if hy : y.length = bitsPerSymbol F then
    List.ofFn (Rf F (fun i => y[i.val]'(by rw [hy]; exact i.isLt))) else y
noncomputable def RLinv (_c y : List Bool) : List Bool :=
  if hy : y.length = bitsPerSymbol F then
    List.ofFn (Rinv F (fun i => y[i.val]'(by rw [hy]; exact i.isLt))) else y





end Fq

namespace QG

variable {n b p w t : ℕ}

/-- Overwrite all `A` blocks of the list. -/
noncomputable def setAll : (Gs : List (QG n b p w t)) → Qubits n → (Fin Gs.length → Qubits w) →
    Qubits n
  | [], z, _ => z
  | G :: Gs, z, y => setE G.aE (setAll Gs z (fun i => y i.succ)) (y 0)









end QG

namespace Fq

variable (F : AvgCaseTI.FieldPres)

open Classical in
/-- The QFT matrix over `F_q` on symbols (zero on invalid symbols). -/
noncomputable def Qq : Matrix (Qubits (bitsPerSymbol F)) (Qubits (bitsPerSymbol F)) ℂ :=
  Matrix.of fun y x => if Valid F y ∧ Valid F x then
    ψ F (decodeElem F y * decodeElem F x) / Real.sqrt (Fintype.card F.F) else 0









end Fq

end OPI
end

-- ===== OPI.CoordQ =====
section

/-!
# The coordinate chain with the kernels of the qubit gadgets

On one coordinate, the gadgets act on pair states `g : K × K → ℂ` by

* `P_β`: `g ↦ g(β − w₁, w₂)` (`pGad_J`);
* `E`: the kernel `kE` (`eGad_J`);
* `QFT_q` on `S` and on `T`: the kernels `kQ false`, `kQ true` of `embedOp_J` with `M = Q_q`.

Starting from `f ⊗ δ₀`, the chain gives `q2 (eOp (pOp β f))`; with `f = Z^c|A_β⟩` this is the ideal
state `psiState β c` (`CoordSym.coord_ideal`).
-/

namespace OPI

namespace SymEnc

open QAlgorithms TwoFoldOPI CoordSym

variable (F : AvgCaseTI.FieldPres)

/-- The kernel of `embedOp (Q_q)` on component `c`. -/
noncomputable def kQ (c : Bool) (w z : F.F × F.F) : ℂ :=
  if z = setComp c w (comp c z) then Fq.Qq F (elemBits F (comp c w)) (elemBits F (comp c z)) else 0









/-- The pair state `f ⊗ δ₀`. -/
noncomputable def withZero (f : F.F → ℂ) (w : F.F × F.F) : ℂ := if w.2 = 0 then f w.1 else 0



/-! ## The encoding of zero -/





/-! ## One coordinate on qubits -/

section Step

variable {n m : ℕ} (reg : Fin m × Bool × Fin (bitsPerSymbol F) ↪ Fin n)





variable (i : Fin m) (ZE asE : List (Fin n)) (aE fE : Fin n)
  (hndE : ([aE] ++ (List.ofFn (bReg reg i false) ++ List.ofFn (bReg reg i true)) ++ ZE ++ asE ++
    [fE]).Nodup) (hZE : 2 * bitsPerSymbol F = ZE.length) (hlenE : 1 + 2 * bitsPerSymbol F ≤ asE.length + 2)
  (houtE : ∀ p, reg p ≠ aE ∧ reg p ≠ fE ∧ (∀ x ∈ ZE, reg p ≠ x) ∧ ∀ x ∈ asE, reg p ≠ x)
  (ZP asP : List (Fin n)) (fP : Fin n)
  (hndP : ([] ++ List.ofFn (bReg reg i false) ++ ZP ++ asP ++ [fP]).Nodup)
  (hZP : bitsPerSymbol F = ZP.length) (hlenP : bitsPerSymbol F ≤ asP.length + 2)
  (houtP : ∀ p, reg p ≠ fP ∧ (∀ x ∈ ZP, reg p ≠ x) ∧ ∀ x ∈ asP, reg p ≠ x)

/-- The ideal operator of coordinate `i`: `P_β`, `E`, then `Q_q` on `S_i` and on `T_i`. -/
noncomputable def coordOp (β : F.F) : Matrix (Qubits n) (Qubits n) ℂ :=
  embedOp (Fq.Qq F) (bReg reg i true) * embedOp (Fq.Qq F) (bReg reg i false) *
    Circuit.unitary (eGad (reg := reg) i ZE asE aE fE) *
    Circuit.unitary (revCirc (pGad reg (elemBits F) i ZP asP fP (fun x => β - x)))



end Step

end SymEnc

end OPI
end

-- ===== OPI.SSA =====
section

/-!
# M3: straight-line programs over a value type, compiled to reversible circuits

A straight-line program is a list of instructions `dst := op (src values)` over values of a type
`V` with a fixed-length binary encoding. Each instruction compiles to one table lookup into a
fresh (clean) register. If the input registers encode an environment `ρ`, the compiled circuit
leaves registers encoding `kRun prog ρ`.
-/

namespace OPI

open QAlgorithms

variable {n : ℕ} {V : Type}

/-- One instruction. -/
structure KIns (V : Type) where
  dst : ℕ
  src : List ℕ
  op : List V → V

/-- Semantics on environments. -/
def kRun : List (KIns V) → (ℕ → V) → ℕ → V
  | [], ρ => ρ
  | I :: Is, ρ => kRun Is (Function.update ρ I.dst (I.op (I.src.map ρ)))

/-- A fixed-length encoding. -/
structure Enc (V : Type) where
  L : ℕ
  enc : V → List Bool
  dec : List Bool → V
  henc : ∀ v, (enc v).length = L
  hdec : ∀ v, dec (enc v) = v

/-- Decode `k` consecutive blocks. -/
def decBlocks (E : Enc V) : ℕ → List Bool → List V
  | 0, _ => []
  | k + 1, bs => E.dec (bs.take E.L) :: decBlocks E k (bs.drop E.L)



/-- The lookup table of an instruction. -/
def tabFn (E : Enc V) (I : KIns V) (bs : List Bool) : List Bool :=
  E.enc (I.op (decBlocks E I.src.length bs))

/-- Compile one instruction. -/
def compIns (E : Enc V) (reg : ℕ → List (Fin n)) (as : List (Fin n)) (f : Fin n) (I : KIns V) :
    List (RGate n) :=
  lookupF (I.src.flatMap reg) (reg I.dst) as f (tabFn E I)

/-- Compile a program. -/
def compile (E : Enc V) (reg : ℕ → List (Fin n)) (as : List (Fin n)) (f : Fin n) (Is : List (KIns V)) :
    List (RGate n) :=
  Is.flatMap (compIns E reg as f)

/-- Register layout for ids `< N`: nodup registers of length `L`, pairwise disjoint, disjoint from
the scratch. -/
structure Layout (E : Enc V) (reg : ℕ → List (Fin n)) (as : List (Fin n)) (f : Fin n) (N : ℕ) :
    Prop where
  len : ∀ i < N, (reg i).length = E.L
  nd : ∀ i < N, (reg i).Nodup
  disj : ∀ i < N, ∀ j < N, i ≠ j → ∀ a ∈ reg i, a ∉ reg j
  scr : ∀ i < N, ∀ a ∈ reg i, a ∉ as ++ [f]
  scrnd : (as ++ [f]).Nodup

/-- `z` encodes `ρ` on the ids in `S`. -/
def Encodes (E : Enc V) (reg : ℕ → List (Fin n)) (S : ℕ → Prop) (ρ : ℕ → V) (z : Qubits n) :
    Prop :=
  ∀ i, S i → (reg i).map z = E.enc (ρ i)

/-- Well-formed programs (all ids `< N`; sources defined and distinct; fresh destinations). -/
def PWF (N : ℕ) : (ℕ → Prop) → List (KIns V) → Prop
  | _, [] => True
  | S, I :: Is => (∀ s ∈ I.src, S s ∧ s < N) ∧ I.src.Nodup ∧ ¬ S I.dst ∧ I.dst < N ∧
      (∀ J ∈ Is, J.dst ≠ I.dst) ∧ PWF N (fun i => S i ∨ i = I.dst) Is







end OPI
end

-- ===== OPI.SSAFix =====
section

/-!
# Straight-line programs: equational semantics and a time-stamp criterion

* `kRun_fix`: in a well-formed program every instruction's equation holds in the final
  environment, `ρ' I.dst = I.op (I.src.map ρ')`, and other ids keep their input values.
* `pwf_of_time`: a program is well-formed if each instruction's sources are inputs or
  destinations with a smaller time stamp, destinations are distinct and fresh, and the
  instructions are listed in non-decreasing time order.
-/

namespace OPI

variable {V : Type}









/-! ## The time-stamp criterion -/

/-- Time-stamp conditions: `time` orders the ids; inputs are `S`. -/
structure TimeOK (N : ℕ) (S : ℕ → Prop) (time : ℕ → ℕ) (Is : List (KIns V)) : Prop where
  src : ∀ I ∈ Is, ∀ s ∈ I.src, (S s ∨ ∃ J ∈ Is, J.dst = s) ∧ time s < time I.dst ∧ s < N
  srcnd : ∀ I ∈ Is, I.src.Nodup
  fresh : ∀ I ∈ Is, ¬ S I.dst
  lt : ∀ I ∈ Is, I.dst < N
  nd : (Is.map KIns.dst).Nodup
  sorted : Is.Pairwise fun I J => time I.dst ≤ time J.dst



end OPI
end

-- ===== OPI.GEProg =====
section

/-!
# Oblivious Gauss–Jordan elimination as a straight-line program

The elimination of `GE.lean` (rows `R`, unknowns `C`, augmented column `C`) written as a list of
`KIns` instructions over the field, followed by the particular solution and a linear output
map `out o = Σ_{j < Kd} x_j · coef j o`.

Ids are laid out as `t · W + offset`, where `t` is a time stamp: every source of an instruction
has a smaller time stamp than its destination, and within one time stamp the offsets increase
along the list. Hence destinations strictly increase along the program.

Flags (`used`, `found`, `selected`) are field elements `0`/`1`.
-/

namespace OPI

namespace GEP

variable {K : Type} [Field K] [DecidableEq K]

section Ids

variable (R C : ℕ)

/-- Index bound. -/
def Bd : ℕ := R + C + 2

/-- Ids per time stamp. -/
def Wd : ℕ := 2 * (Bd R C * Bd R C)

/-- The id with time `t`, kind `k ∈ {0,1}` and indices `a, b < Bd`. -/
def nid (t k a b : ℕ) : ℕ := t * Wd R C + (k * (Bd R C * Bd R C) + a * Bd R C + b)

/-- Start of the step for column `j`. -/
def Tj (j : ℕ) : ℕ := 2 + j * (2 * R + 3)

/-- Matrix entries before step `j`. -/
def idA (j i l : ℕ) : ℕ := nid R C (Tj R j - 1) 0 i l
/-- Used flags before step `j`. -/
def idU (j i : ℕ) : ℕ := nid R C (Tj R j - 1) 1 i 0
/-- Found flags in step `j` (a candidate among the first `i` rows). -/
def idF (j i : ℕ) : ℕ := nid R C (Tj R j + i) 1 0 0
/-- Selection flags in step `j`. -/
def idS (j i : ℕ) : ℕ := nid R C (Tj R j + 1 + i) 0 0 0
/-- Partial pivot rows in step `j`. -/
def idP (j i l : ℕ) : ℕ := nid R C (if i = 0 then Tj R j else Tj R j + R + i) 0 0 l
/-- Normalized pivot row in step `j`. -/
def idN (j l : ℕ) : ℕ := nid R C (Tj R j + 2 * R + 1) 0 0 l
/-- Partial sums of the solution. -/
def idX (j i : ℕ) : ℕ := nid R C (Tj R C + i) 0 j 0
/-- Partial sums of the output. -/
def idO (o jj : ℕ) : ℕ := nid R C (Tj R C + R + 1 + jj) 0 o 0

lemma Bd_pos : 0 < Bd R C := by unfold Bd; omega

lemma off_lt {k a b : ℕ} (hk : k ≤ 1) (ha : a < Bd R C) (hb : b < Bd R C) :
    k * (Bd R C * Bd R C) + a * Bd R C + b < Wd R C := by
  unfold Wd
  have h1 : a * Bd R C + b < Bd R C * Bd R C := by nlinarith
  have h2 : k * (Bd R C * Bd R C) ≤ Bd R C * Bd R C := by nlinarith
  omega

lemma nid_div {t k a b : ℕ} (hk : k ≤ 1) (ha : a < Bd R C) (hb : b < Bd R C) :
    nid R C t k a b / Wd R C = t := by
  unfold nid
  have hW : 0 < Wd R C := by
    have := off_lt R C (k := 0) (a := 0) (b := 0) (Nat.zero_le 1) (Bd_pos R C) (Bd_pos R C); omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt (off_lt R C hk ha hb), zero_add]

lemma nid_mod {t k a b : ℕ} (hk : k ≤ 1) (ha : a < Bd R C) (hb : b < Bd R C) :
    nid R C t k a b % Wd R C = k * (Bd R C * Bd R C) + a * Bd R C + b := by
  unfold nid
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (off_lt R C hk ha hb)]

lemma nid_inj {t k a b t' k' a' b' : ℕ} (hk : k ≤ 1) (ha : a < Bd R C) (hb : b < Bd R C)
    (hk' : k' ≤ 1) (ha' : a' < Bd R C) (hb' : b' < Bd R C)
    (h : nid R C t k a b = nid R C t' k' a' b') : t = t' ∧ k = k' ∧ a = a' ∧ b = b' := by
  have ht : t = t' := by rw [← nid_div R C (t := t) hk ha hb, h, nid_div R C hk' ha' hb']
  have ho : nid R C t k a b % Wd R C = nid R C t' k' a' b' % Wd R C := by rw [h]
  rw [nid_mod R C hk ha hb, nid_mod R C hk' ha' hb'] at ho
  have hB := Bd_pos R C
  have e1 : (k * (Bd R C * Bd R C) + a * Bd R C + b) % Bd R C = b := by
    rw [show k * (Bd R C * Bd R C) + a * Bd R C + b = b + (k * Bd R C + a) * Bd R C by ring,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  have e1' : (k' * (Bd R C * Bd R C) + a' * Bd R C + b') % Bd R C = b' := by
    rw [show k' * (Bd R C * Bd R C) + a' * Bd R C + b' = b' + (k' * Bd R C + a') * Bd R C by ring,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb']
  have e2 : (k * (Bd R C * Bd R C) + a * Bd R C + b) / Bd R C = k * Bd R C + a := by
    rw [show k * (Bd R C * Bd R C) + a * Bd R C + b = b + (k * Bd R C + a) * Bd R C by ring,
      Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hb, zero_add]
  have e2' : (k' * (Bd R C * Bd R C) + a' * Bd R C + b') / Bd R C = k' * Bd R C + a' := by
    rw [show k' * (Bd R C * Bd R C) + a' * Bd R C + b' = b' + (k' * Bd R C + a') * Bd R C by ring,
      Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hb', zero_add]
  have hbb : b = b' := by rw [← e1, ho, e1']
  have hka : k * Bd R C + a = k' * Bd R C + a' := by rw [← e2, ho, e2']
  have haa : a = a' := by
    have : (Bd R C * k + a) % Bd R C = (Bd R C * k' + a') % Bd R C := by
      rw [Nat.mul_comm (Bd R C) k, Nat.mul_comm (Bd R C) k', hka]
    rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at this
    exact this
  have hkk : k = k' := by
    rw [haa] at hka
    have := Nat.add_right_cancel hka
    exact Nat.eq_of_mul_eq_mul_right hB this
  exact ⟨ht, hkk, haa, hbb⟩

end Ids

section Prog

variable (R C Kd : ℕ) (coef : ℕ → ℕ → K) (a0src : ℕ → ℕ → List ℕ) (a0op : ℕ → ℕ → List K → K)

def insA0 (i l : ℕ) : KIns K := ⟨idA R C 0 i l, a0src i l, a0op i l⟩
def insU0 (i : ℕ) : KIns K := ⟨idU R C 0 i, [], fun _ => 0⟩
def insF0 (j : ℕ) : KIns K := ⟨idF R C j 0, [], fun _ => 0⟩
def insP0 (j l : ℕ) : KIns K := ⟨idP R C j 0 l, [], fun _ => 0⟩

def opS : List K → K
  | [a, u, f] => if a ≠ 0 ∧ u = 0 ∧ f = 0 then 1 else 0
  | _ => 0
def insS (j i : ℕ) : KIns K := ⟨idS R C j i, [idA R C j i j, idU R C j i, idF R C j i], opS⟩

def opF : List K → K
  | [a, u, f] => if f ≠ 0 ∨ (a ≠ 0 ∧ u = 0) then 1 else 0
  | _ => 0
def insF (j i : ℕ) : KIns K := ⟨idF R C j (i + 1), [idA R C j i j, idU R C j i, idF R C j i], opF⟩

def opP : List K → K
  | [s, a, p] => p + if s ≠ 0 then a else 0
  | _ => 0
def insP (j i l : ℕ) : KIns K := ⟨idP R C j (i + 1) l, [idS R C j i, idA R C j i l, idP R C j i l], opP⟩

def opN1 : List K → K
  | [p] => p⁻¹ * p
  | _ => 0
def opN2 : List K → K
  | [p, pl] => p⁻¹ * pl
  | _ => 0
def insN (j l : ℕ) : KIns K :=
  if l = j then ⟨idN R C j l, [idP R C j R j], opN1⟩
  else ⟨idN R C j l, [idP R C j R j, idP R C j R l], opN2⟩

def opA1 : List K → K
  | [s, b, nn] => if s ≠ 0 then nn else b - b * nn
  | _ => 0
def opA2 : List K → K
  | [s, a, b, nn] => if s ≠ 0 then nn else a - b * nn
  | _ => 0
def insA (j i l : ℕ) : KIns K :=
  if l = j then ⟨idA R C (j + 1) i l, [idS R C j i, idA R C j i j, idN R C j l], opA1⟩
  else ⟨idA R C (j + 1) i l, [idS R C j i, idA R C j i l, idA R C j i j, idN R C j l], opA2⟩

def opU : List K → K
  | [u, s] => if u ≠ 0 ∨ s ≠ 0 then 1 else 0
  | _ => 0
def insU (j i : ℕ) : KIns K := ⟨idU R C (j + 1) i, [idU R C j i, idS R C j i], opU⟩

def insX0 (j : ℕ) : KIns K := ⟨idX R C j 0, [], fun _ => 0⟩
def insX (j i : ℕ) : KIns K := ⟨idX R C j (i + 1), [idS R C j i, idA R C C i C, idX R C j i], opP⟩

def insO0 (o : ℕ) : KIns K := ⟨idO R C o 0, [], fun _ => 0⟩
def opO (c : K) : List K → K
  | [y, x] => y + x * c
  | _ => 0
def insO (o jj : ℕ) : KIns K := ⟨idO R C o (jj + 1), [idO R C o jj, idX R C jj R], opO (coef jj o)⟩

/-- The instructions with time stamp `t`. -/
def stage (t : ℕ) : List (KIns K) :=
  if t = 1 then
    (List.range R).flatMap (fun i => (List.range (C + 1)).map (insA0 R C a0src a0op i)) ++
      (List.range R).map (insU0 R C)
  else if t < 2 then []
  else if t < Tj R C then
    if (t - 2) % (2 * R + 3) = 0 then
      (List.range (C + 1)).map (insP0 R C ((t - 2) / (2 * R + 3))) ++ [insF0 R C ((t - 2) / (2 * R + 3))]
    else if (t - 2) % (2 * R + 3) ≤ R then
      [insS R C ((t - 2) / (2 * R + 3)) ((t - 2) % (2 * R + 3) - 1),
        insF R C ((t - 2) / (2 * R + 3)) ((t - 2) % (2 * R + 3) - 1)]
    else if (t - 2) % (2 * R + 3) ≤ 2 * R then
      (List.range (C + 1)).map (insP R C ((t - 2) / (2 * R + 3)) ((t - 2) % (2 * R + 3) - R - 1))
    else if (t - 2) % (2 * R + 3) = 2 * R + 1 then
      (List.range (C + 1)).map (insN R C ((t - 2) / (2 * R + 3)))
    else
      (List.range R).flatMap (fun i => (List.range (C + 1)).map (insA R C ((t - 2) / (2 * R + 3)) i)) ++
        (List.range R).map (insU R C ((t - 2) / (2 * R + 3)))
  else if t ≤ Tj R C + R then
    if t = Tj R C then (List.range C).map (insX0 R C)
    else (List.range C).map (fun j => insX R C j (t - Tj R C - 1))
  else if t ≤ Tj R C + R + 1 + Kd then
    if t = Tj R C + R + 1 then (List.range R).map (insO0 R C)
    else (List.range R).map (fun o => insO R C coef o (t - (Tj R C + R + 1) - 1))
  else []

/-- Number of time stamps. -/
def Tmax : ℕ := Tj R C + R + Kd + 2

/-- **The program.** -/
def prog : List (KIns K) := (List.range (Tmax R C Kd)).flatMap (stage R C Kd coef a0src a0op)

end Prog

/-! ## Membership of each instruction -/

section Mem

variable (R C Kd : ℕ) (coef : ℕ → ℕ → K) (a0src : ℕ → ℕ → List ℕ) (a0op : ℕ → ℕ → List K → K)

































/-- The instructions of the program, by kind. -/
def Shape (I : KIns K) : Prop :=
  (∃ i l, i < R ∧ l ≤ C ∧ I = insA0 R C a0src a0op i l) ∨
  (∃ i, i < R ∧ I = insU0 R C i) ∨
  (∃ j, j < C ∧ I = insF0 R C j) ∨
  (∃ j l, j < C ∧ l ≤ C ∧ I = insP0 R C j l) ∨
  (∃ j i, j < C ∧ i < R ∧ I = insS R C j i) ∨
  (∃ j i, j < C ∧ i < R ∧ I = insF R C j i) ∨
  (∃ j i l, j < C ∧ i < R ∧ l ≤ C ∧ I = insP R C j i l) ∨
  (∃ j l, j < C ∧ l ≤ C ∧ I = insN R C j l) ∨
  (∃ j i l, j < C ∧ i < R ∧ l ≤ C ∧ I = insA R C j i l) ∨
  (∃ j i, j < C ∧ i < R ∧ I = insU R C j i) ∨
  (∃ j, j < C ∧ I = insX0 R C j) ∨
  (∃ j i, j < C ∧ i < R ∧ I = insX R C j i) ∨
  (∃ o, o < R ∧ I = insO0 R C o) ∨
  (∃ o jj, o < R ∧ jj < Kd ∧ I = insO R C coef o jj)





end Mem

/-! ## Well-formedness -/

section WF

variable (R C Kd : ℕ) (coef : ℕ → ℕ → K) (a0src : ℕ → ℕ → List ℕ) (a0op : ℕ → ℕ → List K → K)

lemma R_lt_Bd : R < Bd R C := by unfold Bd; omega







/-- Time stamps. -/
def tm (x : ℕ) : ℕ := x / Wd R C












































end WF

/-! ## Semantics -/







section Sem

variable {R C Kd : ℕ} {coef : ℕ → ℕ → K} {a0src : ℕ → ℕ → List ℕ} {a0op : ℕ → ℕ → List K → K}
  (E : ℕ → K)
  (hfix : ∀ I ∈ prog R C Kd coef a0src a0op, E I.dst = I.op (I.src.map E))
  (A0 : GE.Aug K R C)
  (hA0 : ∀ i (hi : i < R) l (hl : l ≤ C), E (idA R C 0 i l) = A0 ⟨i, hi⟩ ⟨l, by omega⟩)

omit [DecidableEq K] in
@[simp] lemma ite_ne_zero (p : Prop) [Decidable p] : ((if p then (1 : K) else 0) ≠ 0) ↔ p := by
  split_ifs with h <;> simp [h]

omit [DecidableEq K] in
@[simp] lemma ite_eq_zero (p : Prop) [Decidable p] : ((if p then (1 : K) else 0) = 0) ↔ ¬ p := by
  split_ifs with h <;> simp [h]













end Sem

/-! ## End-to-end -/







end GEP

end OPI
end

-- ===== OPI.RelinProg =====
section

/-!
# The relinearization decoder as a straight-line program

Inputs: the pairs `(x_i, y_i)` at the ids `in1 i`, `in2 i` (time stamp `0`). The program builds the
augmented matrix `Relin.aug bD bW s t` with `s = x + y`, `t = x y`, runs the elimination of
`GEProg`, and outputs `Relin.decode bD bW s t` at the ids `idO m (k + k2) o k`.
-/

namespace OPI

namespace RelinProg

open GEP

variable {K : Type} [Field K] [DecidableEq K] {m k k2 : ℕ}
  (bD : Fin k → Fin m → K) (bW : Fin k2 → Fin m → K)

/-- `bD` on natural indices. -/
def bDn (j o : ℕ) : K := if h : j < k ∧ o < m then bD ⟨j, h.1⟩ ⟨o, h.2⟩ else 0
/-- `bW` on natural indices. -/
def bWn (j o : ℕ) : K := if h : j < k2 ∧ o < m then bW ⟨j, h.1⟩ ⟨o, h.2⟩ else 0

variable (m k k2) in
/-- Input ids. -/
def in1 (i : ℕ) : ℕ := nid m (k + k2) 0 0 i 0
variable (m k k2) in
def in2 (i : ℕ) : ℕ := nid m (k + k2) 0 1 i 0

variable (m k k2) in
def a0src (i l : ℕ) : List ℕ := if l < k ∨ l = k + k2 then [in1 m k k2 i, in2 m k k2 i] else []

def a0op (i l : ℕ) (xs : List K) : K :=
  if l = k + k2 then (match xs with | [x, y] => -(x * y) | _ => 0)
  else if l < k then (match xs with | [x, y] => -((x + y) * bDn bD l i) | _ => 0)
  else bWn bW (l - k) i

/-- **The decoder program.** -/
def decProg : List (KIns K) :=
  prog m (k + k2) k (bDn bD) (a0src m k k2) (a0op bD bW)

/-- Output ids. -/
def outId (o : ℕ) : ℕ := idO m (k + k2) o k





end RelinProg

end OPI
end

-- ===== OPI.Regev =====
section

/-!
# The core of Regev's reduction (linear algebra)

Let `U` be a unitary, `ψ_d` (`d ∈ D`) input vectors, and `out` the value of the decoder's output
register on basis states. Put `a_d = P_{out = d} U ψ_d`, `b_d = U ψ_d − a_d` and
`v = U† Σ_d a_d`. Then:

* `‖v‖² = Σ_d ‖a_d‖²` (the `a_d` live on disjoint output values);
* if `Σ_d ψ_d` is supported on the good basis states, the part of `v` off the good states has
  `‖·‖² ≤ |D| Σ_d ‖b_d‖²`;
* `‖b_d‖² = ‖ψ_d‖² − ‖a_d‖²`.
-/

namespace OPI

open QAlgorithms Matrix

open scoped ComplexConjugate

variable {n : ℕ} {δ : Type*} [DecidableEq δ]

/-- Restriction to the basis states whose output register reads `d`. -/
def projOut (out : Qubits n → δ) (d : δ) (f : Qubits n → ℂ) : Qubits n → ℂ :=
  fun z => if out z = d then f z else 0

/-- Restriction to the basis states outside `good`. -/
def offGood (good : Qubits n → Prop) [DecidablePred good] (f : Qubits n → ℂ) : Qubits n → ℂ :=
  fun z => if good z then 0 else f z









section Core

variable (U : Mat n) (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (D : Finset δ)
  (ψ : δ → Qubits n → ℂ) (out : Qubits n → δ)

/-- The decoded part. -/
noncomputable def aPart (d : δ) : Qubits n → ℂ := projOut out d (U.mulVec (ψ d))

/-- The undecoded part. -/
noncomputable def bPart (d : δ) : Qubits n → ℂ := U.mulVec (ψ d) - aPart U ψ out d

/-- The accepted vector. -/
noncomputable def vAcc : Qubits n → ℂ := Uᴴ.mulVec (∑ d ∈ D, aPart U ψ out d)







end Core

end OPI
end

-- ===== OPI.ClsDec =====
section

/-!
# The classical decoder on symbol configurations

The compiled relinearization program (`RelinProg.decProg`, compiled by `SSA.compile`) maps the
configuration `cfg a` to a configuration whose output registers hold
`Relin.decode bD bW (x + y) (x y)`, where `a i = (x_i, y_i)`. Hence the decoding test after the
classical decoder has weight `Σ_a [decode = d] |F a|²` on `J F`.
-/

namespace OPI

namespace SymEnc

open QAlgorithms GEP RelinProg

variable {n m L k k2 : ℕ} {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {reg : Fin m × Bool × Fin L ↪ Fin n} {enc : K → Qubits L} (dec : Qubits L → K)
  (hdec : ∀ x, dec (enc x) = x)

/-- The straight-line encoding of symbols. -/
def symEnc : Enc K where
  L := L
  enc x := List.ofFn (enc x)
  dec bs := dec (fun j => bs.getD j false)
  henc x := by simp
  hdec x := by
    have : (fun j : Fin L => (List.ofFn (enc x)).getD j false) = enc x := by
      funext j; simp
    simp only [this, hdec]

/-- Number of straight-line ids. -/
def nIds (m k k2 : ℕ) : ℕ := Tmax m (k + k2) k * Wd m (k + k2)

/-- Register layout of the classical decoder. -/
structure ClsLay (reg : Fin m × Bool × Fin L ↪ Fin n) (enc : K → Qubits L) (dec : Qubits L → K)
    (hdec : ∀ x, dec (enc x) = x) (k k2 : ℕ) where
  rs : ℕ → List (Fin n)
  as : List (Fin n)
  f0 : Fin n
  hlay : Layout (symEnc (enc := enc) dec hdec) rs as f0 (nIds m k k2)
  hin1 : ∀ i : Fin m, rs (in1 m k k2 i) = List.ofFn (bReg reg i false)
  hin2 : ∀ i : Fin m, rs (in2 m k k2 i) = List.ofFn (bReg reg i true)
  hfree : ∀ x < nIds m k k2, (∀ i : Fin m, x ≠ in1 m k k2 i ∧ x ≠ in2 m k k2 i) →
    ∀ q ∈ rs x, ∀ p, reg p ≠ q
  hscr : ∀ q ∈ as ++ [f0], ∀ p, reg p ≠ q
  hsz : 4 * L ≤ as.length + 2

variable {dec hdec}

/-- The compiled decoder. -/
noncomputable def clsGates (C : ClsLay reg enc dec hdec k k2) (bD : Fin k → Fin m → K)
    (bW : Fin k2 → Fin m → K) : List (RGate n) :=
  compile (symEnc (enc := enc) dec hdec) C.rs C.as C.f0 (decProg bD bW)

open Classical in
/-- The straight-line inputs of a configuration. -/
noncomputable def rhoOf (a : Fin m → K × K) : ℕ → K := fun x =>
  if h : ∃ i : Fin m, in1 m k k2 i = x then (a (Classical.choose h)).1
  else if h : ∃ i : Fin m, in2 m k k2 i = x then (a (Classical.choose h)).2 else 0

lemma in1_inj : Function.Injective (fun i : Fin m => in1 m k k2 i) := by
  intro i i' h
  have hR := R_lt_Bd m (k + k2)
  have := (nid_inj m (k + k2) (Nat.zero_le 1) (by omega) (Bd_pos _ _) (Nat.zero_le 1) (by omega)
    (Bd_pos _ _) h).2.2.1
  exact Fin.ext this
lemma in2_inj : Function.Injective (fun i : Fin m => in2 m k k2 i) := by
  intro i i' h
  have hR := R_lt_Bd m (k + k2)
  have := (nid_inj m (k + k2) le_rfl (by omega) (Bd_pos _ _) le_rfl (by omega) (Bd_pos _ _) h).2.2.1
  exact Fin.ext this
lemma in1_ne_in2 (i i' : Fin m) : in1 m k k2 i ≠ in2 m k k2 i' := by
  intro h
  have hR := R_lt_Bd m (k + k2)
  have := (nid_inj m (k + k2) (Nat.zero_le 1) (by omega) (Bd_pos _ _) le_rfl (by omega) (Bd_pos _ _) h).2.1
  omega






/-- The decoded output word of a configuration. -/
noncomputable def outDec (C : ClsLay reg enc dec hdec k k2) (z : Qubits n) : Fin m → K :=
  fun o => (symEnc (enc := enc) dec hdec).dec ((C.rs (outId (m := m) (k := k) (k2 := k2) o)).map z)





end SymEnc

end OPI
end

-- ===== OPI.DecIdeal =====
section

/-!
# The ideal decoder and its decoding probability

`idealDec = U_cls · coordOp_{m-1} ⋯ coordOp_0` maps `J (⊗_i (Z^{d_i}|A_{β_i}⟩ ⊗ |0⟩))` to
`U_cls J (⊗_i |ψ_{d_i}⟩)`; its decoding test has weight `≥ 1 − E` for `d ∈ D`.
-/

namespace OPI

namespace SymEnc

open QAlgorithms TwoFoldOPI CoordSym

variable (F : AvgCaseTI.FieldPres) {n m : ℕ} (reg : Fin m × Bool × Fin (bitsPerSymbol F) ↪ Fin n)

/-- Gadget wires of one coordinate. -/
structure CoordWires (reg : Fin m × Bool × Fin (bitsPerSymbol F) ↪ Fin n) (i : Fin m) where
  ZE : List (Fin n)
  asE : List (Fin n)
  aE : Fin n
  fE : Fin n
  hndE : ([aE] ++ (List.ofFn (bReg reg i false) ++ List.ofFn (bReg reg i true)) ++ ZE ++ asE ++
    [fE]).Nodup
  hZE : 2 * bitsPerSymbol F = ZE.length
  hlenE : 1 + 2 * bitsPerSymbol F ≤ asE.length + 2
  houtE : ∀ p, reg p ≠ aE ∧ reg p ≠ fE ∧ (∀ x ∈ ZE, reg p ≠ x) ∧ ∀ x ∈ asE, reg p ≠ x
  ZP : List (Fin n)
  asP : List (Fin n)
  fP : Fin n
  hndP : ([] ++ List.ofFn (bReg reg i false) ++ ZP ++ asP ++ [fP]).Nodup
  hZP : bitsPerSymbol F = ZP.length
  hlenP : bitsPerSymbol F ≤ asP.length + 2
  houtP : ∀ p, reg p ≠ fP ∧ (∀ x ∈ ZP, reg p ≠ x) ∧ ∀ x ∈ asP, reg p ≠ x

variable {F reg}

/-- The ideal operator of a coordinate with its wires. -/
noncomputable def cOp {i : Fin m} (W : CoordWires F reg i) (β : F.F) : Matrix (Qubits n) (Qubits n) ℂ :=
  coordOp F reg i W.ZE W.asE W.aE W.fE W.ZP W.asP W.fP β

/-- The ideal operators of the coordinates in a list, head applied last. -/
noncomputable def allOps (W : ∀ i, CoordWires F reg i) (β : Fin m → F.F) :
    List (Fin m) → Matrix (Qubits n) (Qubits n) ℂ
  | [] => 1
  | i :: is => cOp (W i) (β i) * allOps W β is

/-- The initial pair states. -/
noncomputable def g0 (β d : Fin m → F.F) : Fin m → F.F × F.F → ℂ :=
  fun i => withZero F (zOp F (d i) (aState F (β i)))

/-- The ideal pair states. -/
noncomputable def gPsi (β d : Fin m → F.F) : Fin m → F.F × F.F → ℂ := fun i => psiState F (β i) (d i)





end SymEnc

end OPI
end

-- ===== OPI.QFTqGad =====
section

/-!
# M4: the `QFT_q` gadget

Re-encoding (a `permGad` on the symbol register `X`) followed by `QFT_p` gadgets on the `e`
blocks. On `|u_p⟩^{⊗e} ⊗ g` (all `B` registers in `|u_p⟩`, `X` valid) it implements
`embedOp (Qq F) X` up to `e · (2π/2^b + 2p/√(2^t))`.
-/

namespace OPI

open QAlgorithms TwoFoldOPI Matrix

variable {n b : ℕ}

/-- Data of a `QFT_q` gadget. -/
structure QQ (n b : ℕ) (F : AvgCaseTI.FieldPres) (t : ℕ) where
  X : Fin (bitsPerSymbol F) ↪ Fin n
  Gs : List (QG n b F.p (Fq.w F) t)
  hlen : Gs.length = F.f.natDegree
  haE : ∀ j : Fin Gs.length, (Gs.get j).aE = (Fq.blk F (Fin.cast hlen j)).trans X
  hpair : List.Pairwise QG.Cross Gs
  cl : List (Fin n)
  hcl : ∀ G ∈ Gs, G.clG = cl
  ZR : List (Fin n)
  asR : List (Fin n)
  fR : Fin n
  hZR : ZR.length = bitsPerSymbol F
  hasR : bitsPerSymbol F ≤ asR.length + 2
  hndR : (List.ofFn X ++ ZR ++ asR ++ [fR]).Nodup
  hRcl : ∀ a ∈ ZR ++ asR ++ [fR], a ∈ cl
  hXcl : ∀ i, X i ∉ cl
  hXb : ∀ G ∈ Gs, ∀ i j, X i ≠ G.bE j
  hXc : ∀ G ∈ Gs, ∀ i j, X i ≠ G.cE j



namespace QQ

variable {F : AvgCaseTI.FieldPres} {t : ℕ} (Q : QQ n b F t)

/-- The re-encoding circuit. -/
noncomputable def RLL : List (RGate n) :=
  permGad [] (List.ofFn Q.X) Q.ZR Q.asR Q.fR (Fq.RL F) (Fq.RLinv F)

noncomputable def PR : Mat n := phPerm (revEquiv Q.RLL) 0

/-- **The `QFT_q` gadget.** -/
noncomputable def circ : Circuit htcxGateSet (n + b) :=
  relocCirc (sysEmb (b := b)) (revCirc Q.RLL) ++ QG.circAll Q.Gs

noncomputable def U : Mat n := QG.UAll Q.Gs * Q.PR

/-- Clean wires of the re-encoding. -/
def RC (z : Qubits n) : Prop := ∀ a ∈ Q.ZR ++ Q.asR ++ [Q.fR], z a = false













/-- Concatenate block values. -/
def catB (y : Fin Q.Gs.length → Qubits (Fq.w F)) : Qubits (bitsPerSymbol F) :=
  fun i => y (Fin.cast Q.hlen.symm (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2

























end QQ

end OPI
end



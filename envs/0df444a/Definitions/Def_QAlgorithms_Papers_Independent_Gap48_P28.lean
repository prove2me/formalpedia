-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P28
-- name    : QAlgorithms_Papers_Independent_Gap48_P28
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T23:27:23.658254+00:00
-- url     : https://prove2.me/theorems/d3b53a35-25d7-4502-9a26-5dbb8d52031c
-- title:
--   Definitions for The Quantum Schur Transform: I. Efficient Qudit Circuits
-- statement:
--   The objects the formalized statements of *The Quantum Schur Transform: I. Efficient Qudit Circuits* (arXiv:quant-ph/0601001) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsGZPattern`: PDF pp.10–11, §III B. Row `r` is the partition for U(r+1), padded with zeroes after column r. Each partition has at most n boxes. Adjacent rows interlace in the upper-left subgroup tower. The top shape is allowed to have any size at most n, as required by the truncated model representation.
--   - `GZPattern`: PDF p.11: finite nonnegative GZ chains, including the auxiliary empty shape.
--   - `gzBinaryCode`: PDF p.11, binary storage with the suppressed ceilings restored. A wire is specified by its row, column and within-entry bit. This is a register of d² ceil(log₂(n+1)) wires. Each entry uses the accepted most-significant-bit-first binary encoding.
--   - `gzTableau`: PDF p.11, the tableau corresponding to a GZ chain: a cell is labelled by its first containing row, with row r representing U(r+1). The alphabet Fin d is zero based, so this value represents the source label r+1. The default zero is used only for chains whose top shape is not lambda; the theorem restricts to chains with the specified top shape.
--   - `tableauBinaryCode`: PDF p.11: store the symbol in each cell in ceil(log_2 d) binary wires, using the same most-significant-bit-first convention as the row encoding. The shape is fixed and is not encoded by this register.
--   - `irrepMatrix`: PDF pp.3,13,16–18: actual polynomial U(d)-irrep matrices, expressed in an orthonormal basis of the accepted Young-image Schur module. For this exact algebraic result the orthonormal bases may be chosen freely, before T; no algorithmic GZ-basis or circuit-synthesis claim is made by this definition.
--   - `intertwinerSpace`: PDF p.17, Eq.(39): the full space Hom(Q_mu tensor Q_nu,Q_lambda)^U(d), not a supplied expansion of the tensor operator to be analyzed.
--   - `cgBlockEntry`: PDF p.13, Eq.(32), and p.17, Eq.(44). The CG lambda block is fixed by the adjoints of a chosen basis of projection intertwiners. Thus its entry is a(q_lambda,(q_mu,q_nu)); the synthesis block is the conjugate transpose. The theorem separately requires the source's coisometry normalization.
-- source:
--   The Quantum Schur Transform: I. Efficient Qudit Circuits, arXiv:quant-ph/0601001v1, https://arxiv.org/abs/quant-ph/0601001v1

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_SchurModules
import Definitions.Def_QAlgorithms_Defs_SchurCharacters

/-!
Statements from Bacon, Chuang and Harrow, quant-ph/0601001v1.
Circuit nodes requiring a concrete phase-compatible GZ/YY target are deferred in
this unit's HARD.md. No arbitrary Schur coordinates are substituted for them.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P28

open scoped Matrix Kronecker ComplexConjugate

/-- PDF pp.10–11, §III B. Row `r` is the partition for U(r+1), padded with
zeroes after column r. Each partition has at most n boxes. Adjacent rows
interlace in the upper-left subgroup tower. The top shape is allowed to have
any size at most n, as required by the truncated model representation. -/
def IsGZPattern {n d : ℕ} (q : Fin d → Fin d → Fin (n + 1)) : Prop :=
  (∀ r c, r.val < c.val → (q r c).val = 0) ∧
  (∀ r a b, a.val ≤ b.val → (q r b).val ≤ (q r a).val) ∧
  (∀ r, (∑ c : Fin d, (q r c).val) ≤ n) ∧
  (∀ r s c e, s.val = r.val + 1 → c.val ≤ r.val → e.val = c.val + 1 →
    (q r c).val ≤ (q s c).val ∧ (q s e).val ≤ (q r c).val)

/-- PDF p.11: finite nonnegative GZ chains, including the auxiliary empty shape. -/
abbrev GZPattern (n d : ℕ) :=
  {q : Fin d → Fin d → Fin (n + 1) // IsGZPattern q}

/-- PDF p.11, binary storage with the suppressed ceilings restored.
A wire is specified by its row, column and within-entry bit. This is a
register of d² ceil(log₂(n+1)) wires. Each entry uses the accepted
most-significant-bit-first binary encoding. -/
def gzBinaryCode {n d : ℕ} (q : GZPattern n d) :
    (Fin d × Fin d × Fin (Nat.clog 2 (n + 1))) → Bool :=
  fun w => QAlgorithms.natToBits (Nat.clog 2 (n + 1))
    (q.val w.1 w.2.1).val w.2.2

/-- The empty partition at every level is legitimate auxiliary recursion data,
including for n=0. This pins padding, row sizes, and interlacing at zero. -/
example (n d : ℕ) : IsGZPattern (fun _ _ : Fin d => (0 : Fin (n + 1))) := by
  simp [IsGZPattern]

/-- PDF p.11, the tableau corresponding to a GZ chain: a cell is labelled by
its first containing row, with row r representing U(r+1). The alphabet Fin d
is zero based, so this value represents the source label r+1. The default
zero is used only for chains whose top shape is not lambda; the theorem
restricts to chains with the specified top shape. -/
def gzTableau {n d : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    (hd : 0 < d) (q : GZPattern n d) : lambda.val.cells → Fin d :=
  fun a =>
    let row : Fin d := ⟨a.val.1, by
      have hleft : (a.val.1, 0) ∈ lambda.val :=
        lambda.val.up_left_mem (by rfl) (Nat.zero_le _) a.property
      exact (YoungDiagram.mem_iff_lt_colLen.mp hleft).trans_le lambda.property.2⟩
    let candidates : Finset (Fin d) :=
      Finset.univ.filter (fun r => a.val.2 < (q.val r row).val)
    if h : candidates.Nonempty then candidates.min' h else ⟨0, hd⟩

/-- PDF p.11: store the symbol in each cell in ceil(log_2 d) binary wires,
using the same most-significant-bit-first convention as the row encoding.
The shape is fixed and is not encoded by this register. -/
def tableauBinaryCode {n d : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    (t : lambda.val.cells → Fin d) :
    (lambda.val.cells × Fin (Nat.clog 2 d)) → Bool :=
  fun w => QAlgorithms.natToBits (Nat.clog 2 d) (t w.1).val w.2

/-- A one-symbol alphabet assigns label zero to every cell, whether the
first-containing-row set is used or the total-function fallback is used. -/
example {n : ℕ} (lambda : QAlgorithms.Schur.Partition 1 n)
    (q : GZPattern n 1) (a : lambda.val.cells) :
    gzTableau lambda (by decide) q a = 0 := by
  exact Subsingleton.elim _ _

/-- PDF pp.3,13,16–18: actual polynomial U(d)-irrep matrices, expressed in
an orthonormal basis of the accepted Young-image Schur module. For this exact
algebraic result the orthonormal bases may be chosen freely, before T; no
algorithmic GZ-basis or circuit-synthesis claim is made by this definition. -/
def irrepMatrix {d n : ℕ} (shape : QAlgorithms.Schur.Partition d n)
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (QAlgorithms.Schur.schurModule shape))
    (u : Matrix.unitaryGroup (Fin d) ℂ) : Matrix ι ι ℂ :=
  fun a c => inner ℂ (b a)
    (QAlgorithms.Schur.polynomialRepresentation shape
      (u : Matrix (Fin d) (Fin d) ℂ) (b c))

/-- PDF p.17, Eq.(39): the full space Hom(Q_mu tensor Q_nu,Q_lambda)^U(d),
not a supplied expansion of the tensor operator to be analyzed. -/
def intertwinerSpace {G M N L : Type*}
    [Fintype M] [Fintype N] [Fintype L]
    (rMu : G → Matrix M M ℂ) (rNu : G → Matrix N N ℂ)
    (rLambda : G → Matrix L L ℂ) :
    Submodule ℂ (Matrix L (M × N) ℂ) where
  carrier := {a | ∀ g, rLambda g * a = a * (rMu g ⊗ₖ rNu g)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb g
    simp only [Matrix.mul_add, Matrix.add_mul, ha g, hb g]
  smul_mem' := by
    intro c a ha g
    simpa only [Matrix.mul_smul, Matrix.smul_mul] using
      congrArg (fun a => c • a) (ha g)

/-- PDF p.13, Eq.(32), and p.17, Eq.(44). The CG lambda block is fixed by
the adjoints of a chosen basis of projection intertwiners. Thus its entry is
a(q_lambda,(q_mu,q_nu)); the synthesis block is the conjugate transpose.
The theorem separately requires the source's coisometry normalization. -/
def cgBlockEntry {G M N L A : Type*}
    [Fintype M] [Fintype N] [Fintype L]
    {rMu : G → Matrix M M ℂ} {rNu : G → Matrix N N ℂ}
    {rLambda : G → Matrix L L ℂ}
    (b : Module.Basis A ℂ (intertwinerSpace rMu rNu rLambda))
    (a : A) (qLambda : L) (qMu : M) (qNu : N) : ℂ :=
  (b a).val qLambda (qMu, qNu)

/-- Eq.(32) sanity check: synthesis conjugates the analysis coefficient.
This fixes the adjoint direction even for complex entries. -/
example {G M N L A : Type*} [Fintype M] [Fintype N] [Fintype L]
    {rMu : G → Matrix M M ℂ} {rNu : G → Matrix N N ℂ}
    {rLambda : G → Matrix L L ℂ}
    (b : Module.Basis A ℂ (intertwinerSpace rMu rNu rLambda))
    (a : A) (qLambda : L) (qMu : M) (qNu : N) :
    ((b a).val)ᴴ (qMu, qNu) qLambda =
      star (cgBlockEntry b a qLambda qMu qNu) := by
  rfl

end QAlgorithms.Papers.Independent.Gap48.P28



-- Prove2me | Definitions.Def_CutRankSched_Supplement_extract
-- name    : CutRankSched_Supplement_extract
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:40:58.736579+00:00
-- url     : https://prove2.me/theorems/a67da4a7-fcd0-4936-8318-789e0c88b17a
-- title:
--   Tableau extraction of the signed Pauli labels of a Clifford+$T$ circuit
-- statement:
--   The **extraction** of a Clifford+$T/T^\dagger$ circuit is the list of signed Pauli labels computed by the recursion in the proof of Theorem 4.1. Scan the gates in circuit order, keeping a Clifford tableau of the current frame $F_s$ (the product of the Clifford gates seen so far): the images $F_s^\dagger X_qF_s$ and $F_s^\dagger Z_qF_s$ of all generators, each as a phased Pauli $i^kX^xZ^z$.
--
--   1. On a Clifford gate $C$, set $F_{s+1}=CF_s$ and update the tableau from $C^\dagger g C$: for $H_q$, $X_q\leftrightarrow Z_q$; for $S_q$, $X_q\mapsto i^3X_qZ_q$ and $Z_q\mapsto Z_q$; for $\mathrm{CNOT}_{c,t}$, $X_c\mapsto X_cX_t$ and $Z_t\mapsto Z_cZ_t$; all other generators are fixed. Products use $(i^kX^xZ^z)(i^{k'}X^{x'}Z^{z'}) = i^{k+k'+2\,z\cdot x'}X^{x+x'}Z^{z+z'}$.
--   2. On $T_q$ (sign $\epsilon=+1$) or $T^\dagger_q$ ($\epsilon=-1$), read $F_s^\dagger Z_qF_s = (-1)^\eta P(p)$ off the tableau and append the label $(\epsilon(-1)^\eta, p)$; the frame is unchanged.
--
--   The result has exactly one label per $T/T^\dagger$ gate, in circuit order: no occurrence is deleted, merged or absorbed into the frame.
--
--   **Formalization Note** A computable function on gate lists (checked on small circuits in the sanity file). This is the reading of "the signs and Pauli labels can be computed exactly by Clifford-tableau updates without deleting an occurrence".
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 4.1 and its proof, p.6

import Mathlib
import Definitions.Def_CutRankSched_Pauli
import Definitions.Def_CutRankSched_Supplement_Gate

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- A phased Pauli `(k, x, z)` stands for the operator `i^k X^x Z^z` (tableau entry). -/
abbrev PhPauli (m : ℕ) : Type := ZMod 4 × Pauli m

/-- Product of phased Paulis: `(i^k X^x Z^z)(i^{k'} X^{x'} Z^{z'}) = i^{k+k'+2(z·x')} X^{x+x'} Z^{z+z'}`. -/
def phMul {m : ℕ} (a b : PhPauli m) : PhPauli m :=
  (a.1 + b.1 + 2 * ((dotProduct a.2.2 b.2.1).val : ZMod 4), (a.2.1 + b.2.1, a.2.2 + b.2.2))

/-- A Clifford tableau: for the current frame `F_s`, the images `F_s† X_q F_s` and `F_s† Z_q F_s`
of every generator, as phased Paulis. -/
abbrev Tableau (m : ℕ) : Type := (Fin m → PhPauli m) × (Fin m → PhPauli m)

/-- The tableau of `F_0 = I`. -/
def Tableau.init (m : ℕ) : Tableau m :=
  (fun q => (0, (Pi.single q 1, 0)), fun q => (0, (0, Pi.single q 1)))

/-- Tableau update `F_{s+1} = C F_s` for a Clifford gate `C`, from `C† g C`:
`H: X ↦ Z, Z ↦ X`; `S: X ↦ i³XZ, Z ↦ Z`; `CNOT_{c,t}: X_c ↦ X_cX_t, Z_t ↦ Z_cZ_t`
(other generators fixed). Non-Clifford gates leave the tableau unchanged. -/
def Tableau.update {m : ℕ} (tb : Tableau m) : Gate m → Tableau m
  | .H q => (Function.update tb.1 q (tb.2 q), Function.update tb.2 q (tb.1 q))
  | .S q => (Function.update tb.1 q
      (let y := phMul (tb.1 q) (tb.2 q); (y.1 + 3, y.2)), tb.2)
  | .CNOT c t _ => (Function.update tb.1 c (phMul (tb.1 c) (tb.1 t)),
      Function.update tb.2 t (phMul (tb.2 c) (tb.2 t)))
  | .T _ => tb
  | .Tdg _ => tb

/-- The signed Hermitian label of a phased Pauli `i^k X^x Z^z = (−1)^η P(p)`: returns `p` and
whether `η = 1`, with `η` determined by `k − x·z ≡ 2η (mod 4)`. -/
def PhPauli.label {m : ℕ} (a : PhPauli m) : Bool × Pauli m :=
  (decide (a.1 - ((Finset.univ.filter fun q => a.2.1 q = 1 ∧ a.2.2 q = 1).card : ZMod 4) = 2),
    a.2)

/-- One step of the extraction recursion of the proof of Theorem 4.1 (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 4.1 and its
proof, p.6): a Clifford gate updates the tableau; a gate `T_q` (`ε = +1`) or `T†_q` (`ε = −1`)
emits `(ε·(−1)^η, p)` with `F_s† Z_q F_s = (−1)^η P(p)` read off the tableau. -/
def extractStep {m : ℕ} (st : Tableau m × List (Bool × Pauli m)) (g : Gate m) :
    Tableau m × List (Bool × Pauli m) :=
  match g with
  | .T q => (st.1, st.2 ++ [((st.1.2 q).label.1.xor true, (st.1.2 q).label.2)])
  | .Tdg q => (st.1, st.2 ++ [((st.1.2 q).label.1.xor false, (st.1.2 q).label.2)])
  | g => (st.1.update g, st.2)

/-- **Exact signed Clifford-frame extraction** (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 4.1 and its proof, p.6): the list
`(ε₁, p₁), …, (ε_n, p_n)` of signed Pauli labels computed from a Clifford+T/T† circuit by
Clifford-tableau updates, one entry per `T`/`T†` gate, in circuit order. The sign is a `Bool`
(`true` = `+1`); for `T_q` it is `(−1)^η`, for `T†_q` it is `−(−1)^η`.

**Formalization Note** This is the reading of "the signs and Pauli labels can be computed exactly
by Clifford-tableau updates without deleting an occurrence": a computable recursion that never
merges or drops an occurrence. -/
def extract {m : ℕ} (c : List (Gate m)) : List (Bool × Pauli m) :=
  (c.foldl extractStep (Tableau.init m, [])).2

end Supplement

end CutRankSched



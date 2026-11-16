-- Prove2me | Definitions.Def_OptQJunta_Supplement_TestsJuntaU
-- name    : OptQJunta_Supplement_TestsJuntaU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:12:41.171178+00:00
-- url     : https://prove2.me/theorems/75e30d44-a9cb-4652-99e3-c0879add4036
-- title:
--   Junta Unitary Testing (Problem 5.1) in the standard, controlled and forward-only models
-- statement:
--   Fix $n$, $k$ and $\varepsilon$. A tester for **Junta Unitary Testing** (Problem 5.1) receives query access to an unknown $n$-qubit unitary $U$ and must output YES with probability at least $2/3$ when $U\in\mathcal U_k$ and NO with probability at least $2/3$ when $\mathrm{dist}_{\mathcal U}(U,\mathcal U_k)\ge\varepsilon$; nothing is required for other $U$.
--
--   Three access models (§2.5.2) are used:
--
--   1. **standard**: each query applies $U$ or $U^\dagger$ to the $n$ query qubits;
--   2. **controlled standard**: each query applies the coherent choice $|0\rangle\langle0|\otimes I+|1\rangle\langle1|\otimes U+|2\rangle\langle2|\otimes U^\dagger$ among the identity, $U$ and $U^\dagger$;
--   3. **forward-only**: each query applies $U$.
--
--   A $T$-query algorithm alternates oracle-independent unitaries on the query register and a private workspace with $T$ queries and ends with a computational-basis measurement.
--
--   **Formalization Note** The algorithm is the published `OptQJunta.SamplerAlg` (a fixed call pattern of the oracle and its adjoint, an arbitrary finite workspace $W$, oracle-independent unit start state and unitaries). Private randomness, intermediate measurements and adaptivity are deferred into $W$, and testers are padded to exactly $T$ queries. The adjoint of the controlled select is again a coherent choice among $I$, $U$, $U^\dagger$. Forward-only means every query slot calls $U$.
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), §2.5, p.22; §2.5.2, p.23; Problem 5.1, p.62

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_OptQJunta_SamplerAlg
import Definitions.Def_OptQJunta_Supplement_IsJuntaU

namespace OptQJunta.Supplement

open QAlgorithms OptQJunta

/-- The controlled query of the standard model (Bao, Gao, Yao, *Optimal Quantum Junta Testing*,
preprint, version of November 3, 2026, sha256 a97d09a4…, §2.5.2, p.23: "A controlled query applies
a coherent choice among the identity, the oracle, and, in the standard model, its inverse"):
`|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U + |2⟩⟨2| ⊗ U†` on `ℂ³ ⊗ ℂ^{2^n}`, the control register first.

**Formalization Note** Its adjoint `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U† + |2⟩⟨2| ⊗ U` is again a coherent choice
among `I`, `U`, `U†`, so a `SamplerAlg` calling this matrix and its adjoint makes controlled
standard-model queries only. -/
noncomputable def ctrlSel {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) :
    Matrix (Fin 3 × Qubits n) (Fin 3 × Qubits n) ℂ :=
  Matrix.of fun a b =>
    if a.1 = b.1 then
      (if a.1 = 0 then (1 : Matrix (Qubits n) (Qubits n) ℂ) a.2 b.2
       else if a.1 = 1 then U a.2 b.2 else U.conjTranspose a.2 b.2)
    else 0

/-- **Problem 5.1** (Junta Unitary Testing; Bao–Gao–Yao preprint, version of November 3, 2026, sha256
a97d09a4…, p.62) in the standard model of §2.5.2 (p.23): the `T`-query algorithm `M`, each query a
call of `U` or `U†` on the `n` query qubits, with output bit `out` (`true` = YES), outputs `true` with
probability `≥ 2/3` on every `U ∈ 𝒰_k` and `false` with probability `≥ 2/3` on every unitary `U`
with `dist_𝒰(U, 𝒰_k) ≥ ε`. Nothing is required on other unitaries.

**Formalization Note** `M` is the published `OptQJunta.SamplerAlg` with query register `Qubits n`,
an arbitrary finite workspace `W`, an oracle-independent unit start state, oracle-independent
unitaries and a fixed call pattern of `U`/`U†`. Private randomness, intermediate measurements and
adaptivity are deferred into `W` (deferred measurement, purification), and a tester making at most
`T` queries in every execution is padded to exactly `T`. A forward-only algorithm is one with
`∀ i, M.dir i = false` (only `U` is called). -/
def TestsJuntaU {n : ℕ} {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    (M : SamplerAlg (Qubits n) W T) (out : Qubits n × W → Bool) (k : ℕ) (ε : ℝ) : Prop :=
  (∀ U : Matrix.unitaryGroup (Qubits n) ℂ, IsJuntaU (U : Matrix (Qubits n) (Qubits n) ℂ) k →
      2 / 3 ≤ M.outputProb (U : Matrix (Qubits n) (Qubits n) ℂ) out true) ∧
    (∀ U : Matrix.unitaryGroup (Qubits n) ℂ, FarU (U : Matrix (Qubits n) (Qubits n) ℂ) k ε →
      2 / 3 ≤ M.outputProb (U : Matrix (Qubits n) (Qubits n) ℂ) out false)

/-- **Problem 5.1** (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…, p.62) with
controlled standard-model queries (§2.5.2, p.23): as `TestsJuntaU`, for an algorithm whose query
register is `Fin 3 × Qubits n` and whose oracle is `ctrlSel U`. -/
def CTestsJuntaU {n : ℕ} {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    (M : SamplerAlg (Fin 3 × Qubits n) W T) (out : (Fin 3 × Qubits n) × W → Bool) (k : ℕ)
    (ε : ℝ) : Prop :=
  (∀ U : Matrix.unitaryGroup (Qubits n) ℂ, IsJuntaU (U : Matrix (Qubits n) (Qubits n) ℂ) k →
      2 / 3 ≤ M.outputProb (ctrlSel (U : Matrix (Qubits n) (Qubits n) ℂ)) out true) ∧
    (∀ U : Matrix.unitaryGroup (Qubits n) ℂ, FarU (U : Matrix (Qubits n) (Qubits n) ℂ) k ε →
      2 / 3 ≤ M.outputProb (ctrlSel (U : Matrix (Qubits n) (Qubits n) ℂ)) out false)

/-- The forward-only model (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…,
§2.5.2, p.23: "In the forward-only model, one query applies `U`"): every query slot of `M` calls
`U`, never `U†`. -/
def IsForwardOnly {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] {T : ℕ}
    (M : SamplerAlg V W T) : Prop :=
  ∀ i, M.dir i = false

end OptQJunta.Supplement



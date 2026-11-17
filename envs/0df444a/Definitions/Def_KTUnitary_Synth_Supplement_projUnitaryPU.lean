-- Prove2me | Definitions.Def_KTUnitary_Synth_Supplement_projUnitaryPU
-- name    : KTUnitary_Synth_Supplement_projUnitaryPU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:16:01.74765+00:00
-- url     : https://prove2.me/theorems/0dcbf591-ff56-4c21-9424-3510c44dd1f3
-- title:
--   $\mathsf{projUnitaryP}^{\mathcal O}$ for a unitary oracle $\mathcal O$
-- statement:
--   Let $\mathcal O=\{O_n\}_{n\in\mathbb N}$ be a unitary language used as an oracle. A **projective $\mathcal O$-oracle unitary quantum circuit** is a sequence of explicitly specified unitary gates (entries given by an FPTEAS encoding) and oracle gates from the set
--   $$\{O_n,\;O_n^*,\;O_n^\dagger,\;O_n^{\mathrm T}\}_{n\in\mathbb N},$$
--   with no controlled oracle gate. A unitary language $\mathcal U=\{U_n\}$ lies in $\mathsf{projUnitaryP}^{\mathcal O}$ if there is a time-uniform family $\{C_{n,\varepsilon}\}$ of projective $\mathcal O$-oracle circuits on $n+a(n,\varepsilon)\le\mathrm{poly}(n,\log 1/\varepsilon)$ qubits such that for every $n$ and $\varepsilon$ there is an $a$-qubit **dilation** $\overline U$ of $U_n$, that is a unitary with $\overline U|\psi\rangle|0^a\rangle=(U_n|\psi\rangle)|g\rangle$ for one garbage state $|g\rangle$ and every $|\psi\rangle$, with
--   $$\|\overline U-C_{n,\varepsilon}\|_{\mathrm{op}}\le\varepsilon .$$
--
--   The projective classes forget global phases: a dilation of $U$ with garbage $|g\rangle$ is also a dilation of $\phi U$ with garbage $\phi^*|g\rangle$. This class relative to a general unitary oracle is used in Theorem 5.23.
--
--   **Formalization Note** The precision is $\varepsilon=2^{-l}$, $l\in\mathbb N$ (footnote 4, p. 14); one FPTEAS encoding serves the whole family; the circuit descriptions are computed from $(1^n,1^l)$ by one polynomial-time machine. The body is that of the published clean class with the published `PSPACEOracleSynth.Main.IsDilation` in place of an extension and with controlled oracle gates excluded. For a classical oracle it coincides with the published `PSPACEOracleSynth.Main.projUnitaryP`.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definitions 5.16 and 5.17, p. 21

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_KTUnitary_Synth_HasFPTEAS
import Definitions.Def_KTUnitary_Synth_UCircuit
import Definitions.Def_KTUnitary_Synth_opNorm
import Definitions.Def_KTUnitary_Synth_TimeUniform
import Definitions.Def_PSPACEOracleSynth_Main_Dilation

open QAlgorithms.Complexity QAdvFew.PoQOracle PSPACEOracleSynth.Main

namespace KTUnitary.Synth.Supplement

/-- **The class `projUnitaryP^𝒪` for a unitary oracle `𝒪`** (Kretschmer, Tang, *Unitary Complexity
in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definitions 5.16 and 5.17, p. 21):
"A unitary language `𝒰 = {U_n}` is in `projUnitaryP^𝒪` if there is a time-uniform family of
projective `𝒪`-oracle unitary quantum circuits `{C_{n,ε}}` on `n + a(n, ε) ≤ poly(n, log 1/ε)`
qubits such that for every `n` and `ε`, there is an `a`-qubit dilation `Ū` of `U_n` satisfying
`‖Ū − C_{n,ε}‖_op ≤ ε`."

Here: there are an encoding `f` with an FPTEAS, a family `C n l` of circuits whose descriptions are
computed from `tup [1^n, 1^l]` by one polynomial-time machine, and a polynomial `p`, such that for
all `n`, `l`: every explicit gate of `C n l` is unitary under `f`; no gate of `C n l` is a controlled
oracle gate; `C n l` has `N` qubits with `n ≤ N ≤ n + p(n + l)`; and some dilation `Ū` of `U_n` to
`N` qubits (published `PSPACEOracleSynth.Main.IsDilation`: one garbage state for all inputs) has
`‖Ū − (unitary of C n l with oracle 𝒪)‖_op ≤ 2^{−l}`.

**Formalization Note** The body is that of the published `KTUnitary.Synth.unitaryP 𝒪` with
`IsDilation` in place of `IsExtension` and the gate restriction of Definition 5.16 (no gate of the form `UGate.corac`; the uncontrolled
oracle gates `UGate.orac κ` of all four kinds `κ` are allowed); `ε = 2^{−l}`
(footnote 4, p. 14); one FPTEAS encoding per family. For a classical oracle `A` the published
`PSPACEOracleSynth.Main.projUnitaryP A` is the same class with `emb A`. -/
def projUnitaryPU (O : ULang) : Set ULang :=
  {U | ∃ (f : Str → ℝ) (C : ℕ → ℕ → UCircuit) (p : Polynomial ℕ), HasFPTEAS f ∧
    TimeUniform (fun nl : ℕ × ℕ => tup [unary nl.1, unary nl.2]) (fun nl => (C nl.1 nl.2).code) ∧
    ∀ n l : ℕ, (C n l).Valid f ∧
      (∀ g ∈ (C n l).gates, ¬ ∃ κ m w, g = UGate.corac κ m w) ∧ ∃ h : n ≤ (C n l).N, (C n l).N ≤ n + p.eval (n + l) ∧
      ∃ Ub, IsDilation h (U n : Matrix (Bits n) (Bits n) ℂ) Ub ∧
        opNorm (Ub - (C n l).unitary f O) ≤ (2 : ℝ)⁻¹ ^ l}

end KTUnitary.Synth.Supplement



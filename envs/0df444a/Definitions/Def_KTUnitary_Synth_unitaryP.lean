-- Prove2me | Definitions.Def_KTUnitary_Synth_unitaryP
-- name    : KTUnitary_Synth_unitaryP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:32:40.845384+00:00
-- url     : https://prove2.me/theorems/f9ed0e46-bb1e-4d9c-a6aa-c6186e4a1442
-- title:
--   The class $\mathsf{unitaryP}^{\mathcal O}$
-- statement:
--   Let $\mathcal O$ be a unitary language. A unitary language $\mathcal U=\{U_n\}$ is in $\mathsf{unitaryP}^{\mathcal O}$ if there are an encoding $f$ with an FPTEAS, a time-uniform family $\{C_{n,\varepsilon}\}$ of valid $\mathcal O$-oracle unitary circuits on $n+a(n,\varepsilon)\le n+\mathrm{poly}(n,\log1/\varepsilon)$ qubits, such that for every $n$ and $\varepsilon$ some $a$-qubit extension $\bar U$ of $U_n$ satisfies
--   $$\|\bar U-C_{n,\varepsilon}\|_{\mathrm{op}}\le\varepsilon.$$
--
--   This is the paper's garbage-free polynomial-time unitary class, with polylogarithmic dependence on $1/\varepsilon$.
--
--   **Formalization Note** $\varepsilon=2^{-\lambda}$ for $\lambda\in\mathbb N$ (footnote 4); the family is indexed by $(n,\lambda)$ and its machine reads $(1^n,1^\lambda)$. One FPTEAS encoding serves the whole family. All eight oracle gates of Definition 5.5 are allowed; the oracle's matrices enter only through the circuit's unitary, never through its description.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definitions 5.2 and 5.6, pp. 16, 18

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_KTUnitary_Synth_HasFPTEAS
import Definitions.Def_KTUnitary_Synth_UCircuit
import Definitions.Def_KTUnitary_Synth_IsExtension
import Definitions.Def_KTUnitary_Synth_opNorm
import Definitions.Def_KTUnitary_Synth_TimeUniform

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **The class `unitaryP^𝒪`** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definitions 5.2 and 5.6, pp. 16 and 18): "A unitary language
`𝒰 = {U_n}` is in `unitaryP^𝒪` if there is a time-uniform family of `𝒪`-oracle unitary quantum
circuits `{C_{n,ε}}_{n ∈ ℕ, ε > 0}` on `n + a(n, ε) ≤ poly(n, log 1/ε)` qubits such that for every `n`
and `ε`, there is an `a`-qubit extension `Ū` of `U_n` satisfying `‖Ū − C_{n,ε}‖_op ≤ ε`."

Here: there are an encoding `f` with an FPTEAS, a family `C n l` of circuits whose descriptions are
computed from `tup [1^n, 1^l]` by one polynomial-time machine, and a polynomial `p`, such that for
all `n`, `l`: every explicit gate of `C n l` is unitary under `f`; `C n l` has `N` qubits with
`n ≤ N ≤ n + p(n + l)`; and some extension `Ū` of `U_n` to `N` qubits has
`‖Ū − (unitary of C n l with oracle 𝒪)‖_op ≤ 2^{−l}`.

**Formalization Note** `ε = 2^{−l}` (footnote 4, p. 14). One FPTEAS encoding `f` serves the whole
family (Definition 4.2's "an FPTEAS encoding `f`"). The oracle gates are all eight of Definition 5.5;
the oracle's matrices enter only through `UCircuit.unitary`, never through the descriptions. -/
def unitaryP (O : ULang) : Set ULang :=
  {U | ∃ (f : Str → ℝ) (C : ℕ → ℕ → UCircuit) (p : Polynomial ℕ), HasFPTEAS f ∧
    TimeUniform (fun nl : ℕ × ℕ => tup [unary nl.1, unary nl.2]) (fun nl => (C nl.1 nl.2).code) ∧
    ∀ n l : ℕ, (C n l).Valid f ∧ ∃ h : n ≤ (C n l).N, (C n l).N ≤ n + p.eval (n + l) ∧
      ∃ Ub, IsExtension h (U n : Matrix (Bits n) (Bits n) ℂ) Ub ∧
        opNorm (Ub - (C n l).unitary f O) ≤ (2 : ℝ)⁻¹ ^ l}

end KTUnitary.Synth



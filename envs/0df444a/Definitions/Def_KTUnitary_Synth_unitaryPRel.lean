-- Prove2me | Definitions.Def_KTUnitary_Synth_unitaryPRel
-- name    : KTUnitary_Synth_unitaryPRel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:32:45.596198+00:00
-- url     : https://prove2.me/theorems/c40fcd76-9061-4413-ac4c-3223ca0bba8e
-- title:
--   The class $\mathsf{unitaryP}^R$ for a relation $R$
-- statement:
--   For a relation $R$, a unitary language $\mathcal U$ is in $\mathsf{unitaryP}^R$ if one FPTEAS encoding $f$, one time-uniform circuit family $\{C_{n,\varepsilon}\}$ and one polynomial bound on the ancillas work for **every** witness oracle $W$ of $R$: for all $n,\varepsilon$ and every such $W$, some extension of $U_n$ is $\varepsilon$-close in operator norm to $C_{n,\varepsilon}$ with oracle $W$.
--
--   This is the paper's convention: "$K^R$ means $K$ with access to an arbitrary witness oracle $W$ for $R$, with a fixed $K$ base machine that is correct for any choice of $W$".
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), §7.1, p. 34

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_KTUnitary_Synth_HasFPTEAS
import Definitions.Def_KTUnitary_Synth_UCircuit
import Definitions.Def_KTUnitary_Synth_IsExtension
import Definitions.Def_KTUnitary_Synth_opNorm
import Definitions.Def_KTUnitary_Synth_TimeUniform
import Definitions.Def_KTUnitary_Synth_emb
import Definitions.Def_KTUnitary_Synth_IsWitnessOracle

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **The class `unitaryP^R` for a relation `R`** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), §7.1, p. 34): "when `K` is a complexity
class that can be augmented with an oracle and `R` is a relation, we use `K^R` to mean `K` with
access to an arbitrary witness oracle `W` for `R`, with a fixed `K` base machine that is correct for
any choice of `W`."

Here: one encoding `f` with an FPTEAS, one time-uniform family `C n l` and one polynomial `p` (as in
`unitaryP`) such that for all `n`, `l` the circuit `C n l` is valid with `n ≤ N ≤ n + p(n + l)`, and
for **every** witness oracle `W` of `R`, some extension `Ū` of `U_n` is `2^{−l}`-close in operator norm
to the unitary of `C n l` with oracle `W` (through its embedding).

**Formalization Note** The circuits do not depend on `W`; only the oracle gates' matrices do. -/
def unitaryPRel (R : Set (Str × Str)) : Set ULang :=
  {U | ∃ (f : Str → ℝ) (C : ℕ → ℕ → UCircuit) (p : Polynomial ℕ), HasFPTEAS f ∧
    TimeUniform (fun nl : ℕ × ℕ => tup [unary nl.1, unary nl.2]) (fun nl => (C nl.1 nl.2).code) ∧
    ∀ n l : ℕ, (C n l).Valid f ∧ ∃ h : n ≤ (C n l).N, (C n l).N ≤ n + p.eval (n + l) ∧
      ∀ W : Oracle, IsWitnessOracle W R →
        ∃ Ub, IsExtension h (U n : Matrix (Bits n) (Bits n) ℂ) Ub ∧
          opNorm (Ub - (C n l).unitary f (emb W)) ≤ (2 : ℝ)⁻¹ ^ l}

end KTUnitary.Synth



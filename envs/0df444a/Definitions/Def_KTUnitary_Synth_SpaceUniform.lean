-- Prove2me | Definitions.Def_KTUnitary_Synth_SpaceUniform
-- name    : KTUnitary_Synth_SpaceUniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:27:56.81066+00:00
-- url     : https://prove2.me/theorems/2b75a090-2861-4aec-98b5-186c344b1db5
-- title:
--   Space-uniform family of descriptions
-- statement:
--   A family of descriptions $(d_i)$ with parameter strings $(s_i)$ and lists of gate descriptions $(g_i)$ is **space-uniform** if for some polynomial $p$ and every $i$:
--   1. $|d_i|\le 2^{p(|s_i|)}$;
--   2. every gate description in $g_i$ has length at most $p(|s_i|)$ ("each gate has a polynomial-length description", footnote 5);
--   3. the bits of the descriptions form a language in $\mathsf{PSPACE}$ (without oracle): $(s_i,\mathrm{bin}(j),b)$ is in it exactly when bit $j$ of $d_i$ is $b$.
--
--   **Formalization Note** The paper's definition is a polynomial-space machine with a write-only output tape. The bit-query form is equivalent: such a machine answers a bit query by running and counting output bits, and a bit decider prints the description bit after bit (both bits are rejected past its end).
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.5 and footnote 5, p. 14

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QAdvFew_PoQOracle_PSPACE

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **Space-uniform family of descriptions** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.5 and footnote 5, p. 14): "A
space-uniform family is defined the same way, but with a polynomial-space machine `M`, and with the
restriction that each gate has a polynomial-length description." Footnote 5: "we do not want to
allow the space-uniform machine to output a gate whose FPTEAS encoding is exponentially long."

Here a family is indexed by `i : ι`, with parameter string `idx i`, description `d i` and list of
gate descriptions `g i`. It is space-uniform if there is a polynomial `p` such that for every `i`:
`|d i| ≤ 2^{p(|idx i|)}`; every gate description in `g i` has length at most `p(|idx i|)`; and the
bits of the descriptions form a language in `PSPACE` (without oracle): `tup [idx i, bin(j), b]` is
in it exactly when the `j`-th bit of `d i` is `b`.

**Formalization Note** The bit-query form is equivalent to a polynomial-space machine with a
write-only output tape: such a machine answers a bit query by running and counting output bits,
and a bit decider prints `d i` bit after bit (both bits are rejected past the end of `d i`). The
bound `2^{p}` on `|d i|` is the length a polynomial-space machine can print (p. 16: "the length of
`C_{n,ε}` … at most `2^{poly(n, log 1/ε)}`"). `bin(j) = Nat.bits j`. -/
def SpaceUniform {ι : Type} (idx : ι → Str) (d : ι → Str) (g : ι → List Str) : Prop :=
  ∃ p : Polynomial ℕ,
    (∀ i : ι, (d i).length ≤ 2 ^ p.eval (idx i).length) ∧
    (∀ i : ι, ∀ s ∈ g i, s.length ≤ p.eval (idx i).length) ∧
    ∃ B ∈ PSPACE (fun _ => false), ∀ (i : ι) (j : ℕ) (b : Bool),
      tup [idx i, Nat.bits j, [b]] ∈ B ↔ (d i)[j]? = some b

end KTUnitary.Synth



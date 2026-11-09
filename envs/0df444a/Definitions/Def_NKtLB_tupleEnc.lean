-- Prove2me | Definitions.Def_NKtLB_tupleEnc
-- name    : NKtLB_tupleEnc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:58:33.108848+00:00
-- url     : https://prove2.me/theorems/3b9944bc-9eec-45fb-914f-47513eff6155
-- title:
--   Encoding of a tuple of strings
-- statement:
--   A tuple $(u_1,\dots,u_j)$ of bit strings is encoded as
--   $$
--   \langle u_1,\dots,u_j\rangle=\mathrm{dbl}(u_1)\,01\,\mathrm{dbl}(u_2)\,01\cdots\mathrm{dbl}(u_j)\,01 .
--   $$
--   This encoding is used for the inputs $(1^n,1^m,1^k,x,z)$ of the generator machines of Lemma 31, the input $(1^n,u)$ of the isolation algorithm of Lemma 101, and the pair $(s,y)$ read by a distinguisher in Corollary 104.
--
--   **Formalization Note** The paper leaves tuple encodings implicit ("our results are robust with respect to encoding choices", p.22). This one is uniquely decodable and has linear length.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §3.2–3.3, pp.21–22; Lemma 31, pp.26–27; Lemma 101, p.68; Corollary 104, p.70

import Mathlib
import Definitions.Def_NKtLB_dbl

namespace NKtLB

/-- **Encoding of a tuple of strings** as one string: each component bit-doubled and followed by the
separator `01`. Used for the inputs `(1^n, 1^m, 1^k, x, z)` of the machines of Lemma 31 and
`(1^n, u)` of Lemma 101, and for distinguishers reading `(s, y)` (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Lemma 31, pp.26–27;
Lemma 101, p.68; Corollary 104, p.70).

**Formalization Note.** The paper leaves the encoding of tuples implicit ("our results are robust
with respect to encoding choices", p.22). This one is uniquely decodable and has linear length. -/
def tupleEnc (l : List (List Bool)) : List Bool := l.flatMap (fun s => dbl s ++ [false, true])

end NKtLB



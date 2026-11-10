-- Prove2me | Definitions.Def_AvgWorstGap_pairStr
-- name    : AvgWorstGap_pairStr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:12.008853+00:00
-- url     : https://prove2.me/theorems/d32f1749-9720-470b-9856-aa4a18f6396a
-- title:
--   Binary and unary strings, self-delimiting copies, and the pair encoding
-- statement:
--   Helpers for writing several numbers and strings as one string.
--
--   - $\mathrm{bin}(n)$ is the binary representation of $n$, most significant bit first ($\mathrm{bin}(0)$ is empty); $1^n$ is the unary string of $n$ ones.
--   - $\mathrm{selfDelim}(s)=\mathrm{dbl}(s)\,01$ is a self-delimiting copy of $s$, where $\mathrm{dbl}$ duplicates each bit (the published `NKtLB.dbl`).
--   - The **pair** $(x,y)$ in $\mathrm{pK}^t(x,y)$ (Lemma 3.15) is $\mathrm{selfDelim}(x)\,y$.
--
--   Tuples $(z_1,\dots,z_m)$, such as the instances $(x,1^s,1^t,1^a,1^b)$, the scheme inputs $(x,1^n,1^k)$ and the verifier inputs $(x,y_1,\dots,y_k)$, are encoded by the published `NKtLB.tupleEnc`, $\mathrm{selfDelim}(z_1)\cdots\mathrm{selfDelim}(z_m)$.
--
--   **Formalization Note** The paper fixes no tuple or pair encoding. These are uniquely decodable and of linear length.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), §2.1, p.12 (program format); Lemma 3.15, p.28 (pairs)

import Mathlib
import Definitions.Def_NKtLB_dbl

namespace AvgWorstGap

open NKtLB

/-- The binary representation of `n`, most significant bit first (`0` is the empty string). -/
def bin (n : ℕ) : List Bool := (Nat.bits n).reverse

/-- The unary string `1^n`. -/
def unary (n : ℕ) : List Bool := List.replicate n true

/-- A self-delimiting copy of `s`: `s` bit-doubled, then the delimiter `01` (the same component code
as `NKtLB.tupleEnc`, so `NKtLB.tupleEnc [s] = selfDelim s`). -/
def selfDelim (s : List Bool) : List Bool := dbl s ++ [false, true]

/-- **The pair `(x, y)` as one string**, for `pK^t(x, y)` (Goldberg, Hu, Lu, Lyu, Oliveira, *The Gap
Between Average-Case and Worst-Case Complexity*, arXiv:2610.19162 (version of October 30, 2026),
Lemma 3.15, p.28): `selfDelim x ++ y`, where `selfDelim x` is `x` bit-doubled and closed by `01`.
Also provides `bin n` (binary, most significant bit first) and `unary n = 1^n`, used by the
instance encodings `(x, 1^s, 1^t, …)` and the program format `s1 01 ⟨M⟩ s2 01 α` (p.12).

**Formalization Note.** The paper fixes no pairing; this one is self-delimiting. Tuples of strings
are encoded by the published `NKtLB.tupleEnc` (each component bit-doubled and followed by `01`). -/
def pairStr (x y : List Bool) : List Bool := selfDelim x ++ y

end AvgWorstGap



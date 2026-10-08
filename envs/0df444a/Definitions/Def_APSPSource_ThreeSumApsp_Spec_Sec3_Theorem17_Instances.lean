-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Instances
-- name    : APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Instances
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:23:47.801682+00:00
-- url     : https://prove2.me/theorems/e0a0fa3a-99b5-4da8-add8-9c7342c10f70
-- title:
--   List encodings of triangle-reduction instances and scans
-- statement:
--   Consider three row-major integer edge-weight lists $AB,BC,AC$ for a tripartite graph with $n$ vertices in each part. Let $R_{AC},R_{BC}$ be their residue tables modulo a positive integer $p$, with entries in $\{0,\ldots,p-1\}$. Fix a residue $\rho$ and a piece of third-part vertices $c=c_0,\ldots,c_0+h-1$.
--
--   The bundle defines the $n\times D$ and $D\times n$ zero-one matrices for the reduced instance. A middle index $u<D$ represents $c=c_0+\lfloor u/p\rfloor$ and $\sigma=u\bmod p$; its entries are
--
--   $$X_{a,u}=\mathbf 1\!\left[\lfloor u/p\rfloor<h\ \land\ \sigma=(R_{AC}[a,c]+\rho)\bmod p\right],$$
--   $$Y_{u,b}=\mathbf 1\!\left[\lfloor u/p\rfloor<h\ \land\ \sigma=(-R_{BC}[b,c])\bmod p\right].$$
--
--   The matrices are written row by row. A Boolean scan checks a fixed pair $(a,b)$ against the piece:
--
--   $$\operatorname{scan}(a,b,c_0,h)\iff\exists t<h,\ AB[a,b]+BC[b,c_0+t]+AC[a,c_0+t]=0.$$
--
--   Searching all $a,b<n$ and the full piece $c_0=0,h=n$ gives the direct all-triples zero-triangle test. Missing list entries are read as zero.
--
--   These functions specify the constructed matrices and witness searches; their correspondence to the reduction and their implementation costs are proved separately.
--
--   References:
--
--   1. [Source formalization: reduced matrices and scans](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Instances.lean#L30-L52).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Instances.lean#L30-L52

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The instances and the scans (proofs of Theorems 17 and 19), as functions on lists

The reduction of Theorem 17 makes one instance of Lop-AE-SparseTri for each chunk of a residue class
`W_ϱ` and each piece `C_k` of `C`.  The middle vertices of the instance are the pairs `(c, σ)` with
`c ∈ C_k` and `σ ∈ ℤ_p`.  This file has the two 0/1 matrices of an instance in the form in which a
routine fills them (`xList`, `yList`), the scan of a piece for a witness (`scanHit`), and the search
through all triples for small instances (`hasZero`).

The weights of an instance of Exact Triangle on `n` vertices per part are three lists `AB`, `BC`,
`AC` of `n²` integers: `w(a,b)` at `a n + b`, `w(b,c)` at `b n + c`, `w(a,c)` at `a n + c`.  The
lists `RAC` and `RBC` hold the residues of the weights modulo `p`, and
`S(a,b,c) = w(a,b) + w(b,c) + w(a,c)`.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-- The matrix `X` of the instance for the residue `ϱ` and the piece `{c0, …, c0 + len - 1}`: the
middle vertex `(c, σ)` is the column `(c - c0) p + σ`, and `a ∼ (c, σ)` iff `σ ≡ w(a,c) + ϱ`.  `n`
rows of `D` entries. -/
def xList (n D p c0 len rho : ℕ) (RAC : List ℕ) : List ℤ :=
  (List.range (n * D)).map fun i =>
    if i % D / p < len ∧ i % D % p = (RAC.getD (i / D * n + c0 + i % D / p) 0 + rho) % p then 1
    else 0

/-- The matrix `Y`: `(c, σ) ∼ b` iff `σ ≡ -w(b,c)`.  `D` rows of `n` entries. -/
def yList (n D p c0 len : ℕ) (RBC : List ℕ) : List ℤ :=
  (List.range (D * n)).map fun i =>
    if i / n / p < len ∧ i / n % p = (p - RBC.getD (i % n * n + c0 + i / n / p) 0) % p then 1
    else 0

/-- "scan the piece C_k of its instance for a c with S(a,b,c) = 0". -/
def scanHit (n : ℕ) (AB BC AC : List ℤ) (a b c0 len : ℕ) : Bool :=
  (List.range len).any fun c =>
    AB.getD (a * n + b) 0 + BC.getD (b * n + c0 + c) 0 + AC.getD (a * n + c0 + c) 0 = 0

/-- Whether there is a zero triangle, by trying all triples (proof of Theorem 19: "smaller instances
are solved by brute force"). -/
def hasZero (n : ℕ) (AB BC AC : List ℤ) : Bool :=
  (List.range n).any fun a => (List.range n).any fun b => scanHit n AB BC AC a b 0 n

end ThreeSumApsp.Spec



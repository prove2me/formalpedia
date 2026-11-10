-- Prove2me | Definitions.Def_PPSLattice_HomEval_Valid
-- name    : PPSLattice_HomEval_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:35:01.041844+00:00
-- url     : https://prove2.me/theorems/79948a69-2c97-4c1b-80f5-0f9383a9cf6f
-- title:
--   The two properties of homomorphic computation
-- statement:
--   With a constant $c$: for every prime $q$, all $n,m$ with $m\ge n\lceil\log q\rceil$, every $\ell$, every $\mathbf B\in\mathbb Z_q^{n\times\ell m}$, every single-output circuit $f$ on $\ell$ inputs and every $x\in\{0,1\}^\ell$,
--   $$(\mathbf B-\mathbf x^\top\otimes\mathbf G)\mathbf H_{f,x}=\mathbf B_f-f(x)\mathbf G,\qquad \|\mathbf H_{f,x}\|\le m^{c(d+1)},$$
--   where $\mathbf B_f=\mathrm{EvalF}(\mathbf B,f)$, $\mathbf H_{f,x}=\mathrm{EvalFX}(\mathbf B,f,x)$ and $d$ is the depth of $f$; the bound does not depend on the size of $f$.
--
--   **Formalization Note** $m^{O(d)}$ is written $m^{c(d+1)}$, which stays meaningful at depth $0$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Homomorphic Computation, pp.16–17

import Mathlib
import Definitions.Def_PPSLattice_HomEval
import Definitions.Def_PPSLattice_kronG
import Definitions.Def_PPSLattice_normInf
import Definitions.Def_PPSLattice_circDepth
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The two **properties of homomorphic computation**, with constant `c` in the exponent: for every
prime `q`, all `n, m` with `m ≥ n⌈log q⌉`, every `ℓ`, every `B ∈ Z_q^{n×ℓm}`, every single-output circuit
`f` on `ℓ` inputs and every `x ∈ {0,1}^ℓ`,
1. `(B − x^⊤ ⊗ G) H_{f,x} = B_f − f(x) G`, where `B_f = EvalF(B, f)` and `H_{f,x} = EvalFX(B, f, x)`;
2. `‖H_{f,x}‖ ≤ m^{c·(d+1)}`, where `d` is the depth of `f`, whatever its size.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Homomorphic Computation, properties (1)–(2), pp.16–17 ("for any B, f ∈ F_{d,ℓ},
x ∈ {0,1}^ℓ (1) (B − x^⊤ ⊗ G)H_{f,x} = B_f − f(x)G where B_f = EvalF(B, f), (2) ‖H_{f,x}‖ ≤ m^{O(d)}. In
particular, this is independent of size of f").

**Formalization Note.** `m^{O(d)}` is written `m^{c(d+1)}` with one constant `c`, which stays meaningful at
depth `0`. `f(x)` is the output bit of `f` read in `Z_q`. `Z_q` is a field (`q` prime), as in §3.1. -/
def HomEval.Valid (H : HomEval) (c : ℕ) : Prop :=
  ∀ q n m ell : ℕ, q.Prime → n * Nat.clog 2 q ≤ m →
    ∀ (B : Matrix (Fin n) (Fin (ell * m)) (ZMod q)) (f : RestrictedDec.Circuit) (x : List Bool),
      f.outs.length = 1 → x.length = ell →
        (B - kronG q n m ell x) * H.evalFX q n m ell B f x =
            H.evalF q n m ell B f - (if (f.eval x).headD false then 1 else 0 : ZMod q) • gadget q n m ∧
          normInf (H.evalFX q n m ell B f x) ≤ m ^ (c * (circDepth ell f + 1))

end PPSLattice



-- Prove2me | Definitions.Def_PPSLattice_FigCompilerValid
-- name    : PPSLattice_FigCompilerValid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:37:20.978923+00:00
-- url     : https://prove2.me/theorems/ae342f6f-5926-4046-b90c-81f7b81c86bd
-- title:
--   Valid circuit compiler for Figure 1 with size $s_C$
-- statement:
--   A map $K$ from descriptions of hardwired data to circuits, with a size function $s_C(\lambda,N,n,q)$, is **valid** if
--
--   1. $K$ is computed in polynomial time;
--   2. $1^{s_C}$ is computed in polynomial time from $(1^\lambda,N,1^n,q)$;
--   3. for every prime $q$ (with $m=n\lceil\log q\rceil$), all hardwired values with $i\in[N]$, $\mu\in\{0,1\}^\lambda$ and admissible encoding randomness, the circuit $K(\cdot)$ has at most $s_C(\lambda,N,n,q)$ gates and computes the function of Figure 1 on every input $b\in\{0,1\}^{nm\lceil\log q\rceil}$.
--
--   Since $s_C$ depends only on $(\lambda,N,n,q)$, it does not depend on $S$, $i$ or $\mu$, as Claim 4.11 requires.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Construction 4.6, p.21; Claim 4.11, p.23

import Mathlib
import Definitions.Def_PPSLattice_figOut
import Definitions.Def_PPSLattice_figCode
import Definitions.Def_PPSLattice_circSize
import Definitions.Def_PPSLattice_PolyTimeOn
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- A **valid circuit compiler for Figure 1** with size function `s_C(λ, N, n, q)`:
1. `K` maps the description `figCode …` of the hardwired data to a circuit, in polynomial time (on circuit
   codes);
2. `1^{s_C(λ,N,n,q)}` is computed in polynomial time from `(1^λ, N, 1^n, q)` (`N`, `q` in binary);
3. for every `λ, N, n`, every prime `q` (with `m = n⌈log q⌉`), every hardwired `A, s, e, P, ẽ, tg`, every
   `i ∈ [N]`, every `µ ∈ {0,1}^λ` and every encoding randomness `r` (`⌈log N⌉m + nλ + λ` values in
   `[0, ⌊2^{ℓ_q}/q⌋ − 1]`), the circuit `C = K(figCode …)` has at most `s_C(λ, N, n, q)` gates and computes
   `figOut` on every input `b ∈ {0,1}^{n·m·⌈log q⌉}`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Construction 4.6, p.21 ("Here, s_C is the size of circuit from Figure 1", skEnc Step 2 "Construct the
circuit C from Figure 1"); Claim 4.11, p.23 ("there exists a boolean circuit representation with size
s_C … Moreover, s_C does not depend on S, i, or µ").

**Formalization Note.** `s_C` takes only `(λ, N, n, q)`, so it depends on neither `S`, `i`, `µ` nor the other
hardwired values. Clauses 1–2 are the reading of "Construct the circuit C" inside the polynomial-time
skEnc and of MSKGen's use of `1^{s_C}`. -/
def FigCompilerValid (K : Str → RestrictedDec.Circuit) (sC : ℕ → ℕ → ℕ → ℕ → ℕ) : Prop :=
  PolyTimeOn (fun w : Str => w) (fun w => (K w).code) ∧
    PolyTimeOn (fun a : ℕ × ℕ × ℕ × ℕ =>
        BeyondDS.tup [encNat a.1, encBin a.2.1, encNat a.2.2.1, encBin a.2.2.2])
      (fun a => encNat (sC a.1 a.2.1 a.2.2.1 a.2.2.2)) ∧
    ∀ (lam N n q : ℕ), q.Prime →
      ∀ (A : Matrix (Fin n) (Fin (Nat.clog 2 N * (n * Nat.clog 2 q))) (ZMod q))
        (s : Fin n → ZMod q) (e : Fin (Nat.clog 2 N * (n * Nat.clog 2 q)) → ZMod q)
        (P : Matrix (Fin n) (Fin lam) (ZMod q)) (et tg : Fin lam → ZMod q) (i : ℕ) (mu : Str)
        (r : List ℕ),
        i ∈ Finset.Icc 1 N → mu.length = lam →
        r.length = Nat.clog 2 N * (n * Nat.clog 2 q) + n * lam + lam →
        (∀ x ∈ r, x < 2 ^ (Nat.clog 2 q + lam) / q) →
          circSize (K (figCode lam N n q A s e P et tg i mu r)) ≤ sC lam N n q ∧
            ∀ b : Str, b.length = n * (n * Nat.clog 2 q) * Nat.clog 2 q →
              (K (figCode lam N n q A s e P et tg i mu r)).eval b =
                figOut q n (n * Nat.clog 2 q) N lam A s e P et tg i mu r b

end PPSLattice



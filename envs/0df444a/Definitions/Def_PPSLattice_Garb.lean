-- Prove2me | Definitions.Def_PPSLattice_Garb
-- name    : PPSLattice_Garb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:22.025412+00:00
-- url     : https://prove2.me/theorems/b9cc7edb-ec86-4103-a8bc-847dc255f5f8
-- title:
--   Blind garbled circuit scheme: syntax
-- statement:
--   A **garbling scheme** for the class $\mathcal C_{s,\ell}$ of circuits of size at most $s$ on $\ell$ input bits consists of
--
--   1. $\mathrm{Setup}(1^\lambda,1^s,1^\ell)\to\mathrm{gk}$;
--   2. the deterministic $\mathrm{InpGarb}(\mathrm{gk},x)\to\tilde x$;
--   3. $\mathrm{CircGarb}(\mathrm{gk},C)\to\tilde C$;
--   4. the deterministic $\mathrm{Eval}(\tilde C,\tilde x)\to y$;
--   5. $\mathrm{Sim}(\mathrm{gk},x,C(x))\to\tilde C$;
--   6. the garbled-circuit length $L(\lambda,s,\ell,\ell_{\mathrm{out}})$.
--
--   **Formalization Note** The length $L$ is part of the syntax because MSKGen of Construction 4.6 uses $L_{\tilde C}$ before any circuit is garbled.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.2, p.19; Definition 4.4, p.20; Construction 4.6, p.21

import Mathlib
import Definitions.Def_RestrictedDec_Circuit
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- A **blind garbled circuit scheme** for the class `C_{s,ℓ}` of circuits of size at most `s` on `ℓ`
input bits, by the laws of its algorithms:
1. `setup λ s ℓ`: `Setup(1^λ, 1^s, 1^ℓ) → gk`;
2. `inpGarb gk x`: the deterministic `InpGarb(gk, x) → x̃`;
3. `circGarb gk C`: `CircGarb(gk, C) → C̃`;
4. `eval C̃ x̃`: the deterministic `Eval(C̃, x̃) → y`;
5. `sim gk x y`: `Sim(gk, x, C(x)) → C̃`;
6. `glen λ s ℓ ℓ_out`: the length `L` of a garbled circuit of a circuit with `ℓ_out` output bits.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.2, Blind Garbled Circuits, p.19; Definition 4.4, p.20 ("L is the length of the garbled
circuit of C"); Construction 4.6, p.21 (MSKGen uses `L_C̃` before any circuit is garbled).

**Formalization Note.** Circuits are the multi-output NAND circuits of `RestrictedDec.Circuit`.
`glen` is part of the syntax because Construction 4.6 needs `L_C̃` as a function of the parameters;
`Garb.IsBlindGarb` requires CircGarb to output strings of exactly that length. -/
structure Garb where
  setup : ℕ → ℕ → ℕ → PMF Str
  inpGarb : Str → Str → Str
  circGarb : Str → RestrictedDec.Circuit → PMF Str
  eval : Str → Str → Str
  sim : Str → Str → Str → PMF Str
  glen : ℕ → ℕ → ℕ → ℕ → ℕ

end PPSLattice



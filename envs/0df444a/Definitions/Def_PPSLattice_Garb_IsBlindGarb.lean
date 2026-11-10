-- Prove2me | Definitions.Def_PPSLattice_Garb_IsBlindGarb
-- name    : PPSLattice_Garb_IsBlindGarb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:36:25.528197+00:00
-- url     : https://prove2.me/theorems/40ff35c8-1e80-4830-99cb-f01148c7e7d4
-- title:
--   Blind garbled circuit scheme: Definition 4.4
-- statement:
--   A garbling scheme is a **blind garbled circuit scheme** if, for all $\lambda\ge1$ (§3: $\mathbb N$ is the set of positive integers) and $s,\ell\ge1$, every $\mathrm{gk}$ output by $\mathrm{Setup}(1^\lambda,1^s,1^\ell)$, every circuit $C$ of size at most $s$ with $\ell_{\mathrm{out}}$ outputs and every $x\in\{0,1\}^\ell$:
--
--   1. (length) every $\tilde C$ output by $\mathrm{CircGarb}(\mathrm{gk},C)$ has length $L=L(\lambda,s,\ell,\ell_{\mathrm{out}})$;
--   2. (correctness) $\mathrm{Eval}(\tilde C,\mathrm{InpGarb}(\mathrm{gk},x))=C(x)$ for every $\tilde C$ output by $\mathrm{CircGarb}(\mathrm{gk},C)$;
--   3. (security) every PPT adversary has negligible advantage in the garbling experiment;
--   4. (blindness) $\mathrm{Sim}(\mathrm{gk},x,y)$ with $y\leftarrow\{0,1\}^{\ell_{\mathrm{out}}}$ is uniform on $\{0,1\}^L$.
--
--   **Formalization Note** Blindness is required for every key, as the proof of Lemma 4.22 uses it ("As blindness holds for every garb.gk and every input $\mathbf A_S$"); the printed display draws $\mathrm{gk}\leftarrow\mathrm{Setup}$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.4, p.20; Construction 4.6, p.21; proof of Lemma 4.22, p.29

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_PPSLattice_garbGame
import Definitions.Def_AvgPHETH_uniformDist
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- A garbling scheme is a **blind garbled circuit scheme** (Definition 4.4) for all `s, ℓ ≥ 1`: for
every `gk` output by `Setup(1^λ, 1^s, 1^ℓ)`, every circuit `C` of size at most `s` and every
`x ∈ {0,1}^ℓ`,
1. (length) every `C̃` output by `CircGarb(gk, C)` has length `L = glen(λ, s, ℓ, ℓ_out)`, `ℓ_out` the
   output length of `C`;
2. (correctness) `Eval(C̃, InpGarb(gk, x)) = C(x)` for every `C̃` output by `CircGarb(gk, C)`;
3. (security) every uniform PPT adversary has negligible advantage `|Pr[garbGame = 1] − ½|`;
4. (blindness) `Sim(gk, x, y)` for `y ← {0,1}^{ℓ_out}` is the uniform law on `{0,1}^L`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.4, p.20; Construction 4.6, p.21 (`L_C̃`); proof of Lemma 4.22, p.29 ("As blindness
holds for every garb.gk and every input A_S").

**Formalization Note.** The length, correctness and blindness clauses are stated for `λ ≥ 1`, since `λ ∈ N` ranges over the positive integers (§3, p.15: "We denote … the set of positive integers by N"). Blindness is required for every key in the support of Setup, which is how
the proof of Lemma 4.22 uses it; the printed display draws `gk ← Setup`. The length clause makes `L`
a function of `(λ, s, ℓ, ℓ_out)`, as MSKGen of Construction 4.6 requires. -/
def Garb.IsBlindGarb (G : Garb) : Prop :=
  (∀ lam s ell : ℕ, 1 ≤ lam → 1 ≤ s → 1 ≤ ell → ∀ gk ∈ (G.setup lam s ell).support,
      ∀ C : RestrictedDec.Circuit, circSize C ≤ s →
        ∀ Ct ∈ (G.circGarb gk C).support, Ct.length = G.glen lam s ell C.outs.length) ∧
    (∀ lam s ell : ℕ, 1 ≤ lam → 1 ≤ s → 1 ≤ ell → ∀ gk ∈ (G.setup lam s ell).support,
      ∀ C : RestrictedDec.Circuit, circSize C ≤ s → ∀ x : Str, x.length = ell →
        ∀ Ct ∈ (G.circGarb gk C).support, G.eval Ct (G.inpGarb gk x) = C.eval x) ∧
    (∀ A : RestrictedDec.Adversary, A.Valid →
      NoisyOWMPC.Negligible fun lam => |((garbGame G A lam) true).toReal - 1 / 2|) ∧
    (∀ lam s ell : ℕ, 1 ≤ lam → 1 ≤ s → 1 ≤ ell → ∀ gk ∈ (G.setup lam s ell).support,
      ∀ C : RestrictedDec.Circuit, circSize C ≤ s → ∀ x : Str, x.length = ell →
        (AvgPHETH.uniformDist C.outs.length).bind (G.sim gk x) =
          AvgPHETH.uniformDist (G.glen lam s ell C.outs.length))

end PPSLattice



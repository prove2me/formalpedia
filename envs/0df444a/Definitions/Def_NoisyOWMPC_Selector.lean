-- Prove2me | Definitions.Def_NoisyOWMPC_Selector
-- name    : NoisyOWMPC_Selector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:51:48.779683+00:00
-- url     : https://prove2.me/theorems/f6899024-8fa5-45f2-ab3c-2b98f47347f7
-- title:
--   Recoverable selectors
-- statement:
--   A **selector on $[N]$** with seed length $\kappa_{\mathrm{sel}}$ adds to the protocol half the proof-side algorithms $\mathrm{SampleSt}_{\mathrm{sel}}$, $\mathrm{Recons}_{\mathrm{sel}}(\mathrm{st},\xi)\to K$ and $\mathrm{Rec}_{\mathrm{sel}}(\mathrm{st},V,U)\to\mathcal L$. With $V\subseteq[N]$ the fair set, it is **recoverable with errors $(\alpha_{\mathrm{sel}},\delta_{\mathrm{sel}})$** (Definition 5.4) if
--   1. honest acceptance (5.5) and balance (5.6) hold;
--   2. *sampling correctness* (5.7): $\mathrm{Recons}_{\mathrm{sel}}(\mathrm{st},\xi)\overset d=\mathrm{Gen}_{\mathrm{sel}}(1^\lambda)$;
--   3. *recoverability* (5.8): with $K=\mathrm{Recons}_{\mathrm{sel}}(\mathrm{st},\xi)$,
--   $$\Pr_{\mathrm{st},\xi,V}[\exists U\subseteq V:\mathrm{Guard}_{\mathrm{sel}}(U)=1\text{ and }b_K(U)\ne b_K(V)\text{ and }\xi\notin\mathrm{Rec}_{\mathrm{sel}}(\mathrm{st},V,U)]\le\delta_{\mathrm{sel}};$$
--   4. its algorithms are efficient (polynomial $\kappa_{\mathrm{sel}}$, samplers within $2^{-\lambda}$, deterministic polynomial-time guard, coin, reconstruction and recovery).
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Definition 5.4, p.23

import Mathlib
import Definitions.Def_NoisyOWMPC_Halves
import Definitions.Def_NoisyOWMPC_CoinAlg
import Definitions.Def_QAdvFew_PoQOracle_tup

namespace NoisyOWMPC

open LaconicBarrier

/-- A **selector on `[N]` with seed length `κ_sel`** (Ishai, Lu, Zafar, STOC 2027 submission
(manuscript sha256 3a9569fa…), Definition 5.4, p.23): the protocol half (`Gen_sel`, `Guard_sel`,
`b_K`) and the proof-side algorithms `SampleSt_sel(1^λ) → st` (exact law `sampW λ`),
`Recons_sel(st, ξ) → K` and `Rec_sel(st, V, U) → L` for `U ⊆ V ⊆ [N]`. -/
structure Selector (N : ℕ → ℕ) extends SelHalf N where
  /-- the seed length `κ_sel` -/
  κ : ℕ → ℕ
  /-- the sampler states -/
  St : ℕ → Type
  [finSt : ∀ lam, Fintype (St lam)]
  /-- the law of `SampleSt_sel(1^λ)` -/
  sampW : (lam : ℕ) → St lam → ℝ
  /-- the encoding of a sampler state -/
  encSt : (lam : ℕ) → St lam → List Bool
  /-- `Recons_sel(st, ξ)` -/
  recons : (lam : ℕ) → St lam → (Fin (κ lam) → Bool) → Key lam
  /-- `Rec_sel(st, V, U)` -/
  recov : (lam : ℕ) → St lam → Finset (Fin (N lam)) → Finset (Fin (N lam)) → List (Fin (κ lam) → Bool)

attribute [instance] Selector.finSt

/-- The indicator-vector encoding of a set `U ⊆ [N]`. -/
def setEnc {N : ℕ} (U : Finset (Fin N)) : List Bool := List.ofFn fun v => decide (v ∈ U)

/-- The selector is a **recoverable selector with errors `(α_sel, δ_sel)`** (Definition 5.4,
(5.5)–(5.8), p.23), with efficient algorithms:
1. honest acceptance `Pr[Guard_sel(V) = 0] ≤ α_sel` and balance (5.6) for the fair set `V`;
2. sampling correctness (5.7): `Recons_sel(st, ξ) =ᵈ Gen_sel(1^λ)`;
3. recoverability (5.8): with `K = Recons_sel(st, ξ)`,
   `Pr_{st,ξ,V}[∃ U ⊆ V : Guard_sel(U) = 1 and b_K(U) ≠ b_K(V) and ξ ∉ Rec_sel(st, V, U)] ≤ δ_sel`;
4. efficiency: `κ_sel` polynomial, both samplers' laws probability distributions implementable
   within `2^{−λ}`, injective encodings, and deterministic polynomial-time `Guard_sel`, `b_K`,
   `Recons_sel`, `Rec_sel`. -/
def Selector.IsRecSelector {N : ℕ → ℕ} (S : Selector N) (αsel δsel : ℕ → ℝ) : Prop :=
  S.HonestAccept αsel ∧ S.Balanced ∧
  (∀ lam K, wprob (fun z : S.St lam × (Fin (S.κ lam) → Bool) => S.sampW lam z.1 * (1 / 2 : ℝ) ^ (S.κ lam))
    (fun z => S.recons lam z.1 z.2 = K) = S.genW lam K) ∧
  (∀ lam, wprob (fun z : (S.St lam × (Fin (S.κ lam) → Bool)) × Finset (Fin (N lam)) =>
      S.sampW lam z.1.1 * (1 / 2 : ℝ) ^ (S.κ lam) * fairW (N lam) z.2)
    (fun z => ∃ U ⊆ z.2, S.guard lam U = true ∧
      S.coin lam (S.recons lam z.1.1 z.1.2) U ≠ S.coin lam (S.recons lam z.1.1 z.1.2) z.2 ∧
      z.1.2 ∉ S.recov lam z.1.1 z.2 U) ≤ δsel lam) ∧
  PolyBounded N ∧ PolyBounded S.κ ∧ S.IsDist ∧
  (∀ lam, (∀ st, 0 ≤ S.sampW lam st) ∧ ∑ st, S.sampW lam st = 1) ∧
  (∀ lam, Function.Injective (S.enc lam)) ∧ (∀ lam, Function.Injective (S.encSt lam)) ∧
  Samplable (I := fun _ => Unit) (fun lam _ => S.genW lam) (fun lam _ => S.enc lam) (fun _ _ => []) ∧
  Samplable (I := fun _ => Unit) (fun lam _ => S.sampW lam) (fun lam _ => S.encSt lam)
    (fun _ _ => []) ∧
  PolyTimeOn (ι := (lam : ℕ) × Finset (Fin (N lam))) (fun z => [unary z.1, setEnc z.2])
    (fun z => [S.guard z.1 z.2]) ∧
  PolyTimeOn (ι := (lam : ℕ) × S.Key lam × Finset (Fin (N lam)))
    (fun z => [unary z.1, S.enc z.1 z.2.1, setEnc z.2.2]) (fun z => [S.coin z.1 z.2.1 z.2.2]) ∧
  PolyTimeOn (ι := (lam : ℕ) × S.St lam × (Fin (S.κ lam) → Bool))
    (fun z => [unary z.1, S.encSt z.1 z.2.1, bits z.2.2]) (fun z => S.enc z.1 (S.recons z.1 z.2.1 z.2.2)) ∧
  PolyTimeOn (ι := (lam : ℕ) × S.St lam × Finset (Fin (N lam)) × Finset (Fin (N lam)))
    (fun z => [unary z.1, S.encSt z.1 z.2.1, setEnc z.2.2.1, setEnc z.2.2.2])
    (fun z => QAdvFew.PoQOracle.tup ((S.recov z.1 z.2.1 z.2.2.1 z.2.2.2).map bits))

end NoisyOWMPC



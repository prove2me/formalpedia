-- Prove2me | Definitions.Def_SeededShannon_Supplement_SparseSetObf
-- name    : SeededShannon_Supplement_SparseSetObf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:37:19.254997+00:00
-- url     : https://prove2.me/theorems/a0845c7e-2548-4780-abb7-0571bf1a9203
-- title:
--   Sparse-set and sparse-partition obfuscators as ingredients of Construction 6.1
-- statement:
--   Two evasive obfuscators are ingredients of Construction 6.1.
--
--   1. $(\Pi_{\mathrm{EvObf}},\mathrm{setOf})$ is a **sparse-set obfuscator at density $\delta$ with the parameters of Corollary 5.9** if, with an efficiently computable polynomial minimum input length $N_{\min}$ and an efficiently computable set-size bound $B$ with $B(\lambda,t)\le C_s\cdot t^{3/4}$ for $t\ge N_{\min}(\lambda)$: $\Pi_{\mathrm{EvObf}}$ is a distributional evasive obfuscator (Definition 5.1) for the family $\{f_S:|S|\le B(\lambda,t)\}$, $f_S(x)=1\iff\delta(x)\le\delta\wedge x_S=1$; the map $\mathrm{setOf}$ from sampling seeds to sets runs in time $\mathrm{poly}(\lambda,t)$; and every returned seed $\sigma$ determines a set $S_\sigma$ of size at most $B(\lambda,t)$ with $f_\sigma=f_{S_\sigma}$.
--   2. $(\Pi_{\mathrm{EvObf}},\mathrm{partOf})$ is a **sparse-partition obfuscator at $(p,\tau,\gamma,b)$** if, with an efficiently computable polynomial minimum input length $N_{\min}$ and supported lengths divisible by $b$: $\Pi_{\mathrm{EvObf}}$ is a distributional evasive obfuscator for $\{f_P\}$, $P$ a partition of $[n]$ into $b$-element blocks, $f_P(x)=1\iff x\in\mathrm{Ball}_p(0^n)\setminus\mathrm{Bal}_P(0^n;\tau,\gamma)$; the map $\mathrm{partOf}$ runs in time $\mathrm{poly}(\lambda,n)$; and every returned seed $\sigma$ determines a partition $P_\sigma$ with $f_\sigma=f_{P_\sigma}$.
--
--   These are the objects of the conclusions of the published Theorems 5.2 and 5.3, at the parameters Construction 6.1 uses them.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Construction 6.1, p.37 (PDF p.40); Theorems 5.2, 5.3, pp.31–32; Corollary 5.9, p.34

import Mathlib
import Definitions.Def_SeededShannon_EvObf
import Definitions.Def_SeededShannon_setFamily
import Definitions.Def_SeededShannon_balP

set_option autoImplicit false

namespace SeededShannon.Supplement

open LaconicBarrier NoisyOWMPC SeededShannon

/-- `(Π_EvObf, setOf)` is a **sparse-set obfuscator at density `δ` with the parameters of
Corollary 5.9** (Dujmovic, Lu, Silbak, Wichs, STOC 2027 submission (manuscript sha256
52f4b606…a769709), Construction 6.1, p.37: "Let `Π_EvObf_s` be the sparse-set obfuscator of
Theorem 5.2 at density `p/τ`, using the parameters of Corollary 5.9. Write `B_s(λ, t) ≤ C_s · t^{3/4}`
for its set-size bound, where `C_s` is a constant"): the object of the conclusion of the published
`SeededShannon.theorem_5_2` at density `δ`, with minimum input length `N_min`, an efficiently
computable set-size bound `B` satisfying `B(λ, t) ≤ C_s · t^{3/4}` for `t ≥ N_min(λ)`:
1. `Π_EvObf` is a distributional evasive obfuscator for `{f_S : |S| ≤ B(λ, t)}`, `f_S(x) = 1 ⟺
   δ(x) ≤ δ ∧ x_S = 1`, with minimum input length `N_min`;
2. the map `setOf` from sampling seeds to (indicator vectors of) sets runs in time `poly(λ, t)`;
3. every returned seed `σ` determines a set `S_σ = setOf(σ)` of size at most `B(λ, t)` with
   `f_σ = f_{S_σ}`. -/
def SparseSetObf (δ : ℝ) (Nmin : ℕ → ℕ) (B : ℕ → ℕ → ℕ) (Cs : ℝ) (O : EvObf)
    (setOf : ℕ → ℕ → List Bool → List Bool) : Prop :=
  PolyParam Nmin ∧ EffComputable₂ B ∧
  (∀ lam n, Nmin lam ≤ n → (B lam n : ℝ) ≤ Cs * (n : ℝ) ^ ((3 : ℝ) / 4)) ∧
  O.IsEvObf Nmin (fun _ _ => True) (setFamily δ B) ∧
  PolyTimeOn (ι := (z : {z : ℕ × ℕ // Nmin z.1 ≤ z.2}) × (Fin (O.progCoins z.1.1 z.1.2) → Bool))
    (fun i => [unary i.1.1.1, unary i.1.1.2, (O.genProg i.1.1.1 i.1.1.2 i.2).1])
    (fun i => setOf i.1.1.1 i.1.1.2 (O.genProg i.1.1.1 i.1.1.2 i.2).1) ∧
  ∀ lam n, Nmin lam ≤ n → ∀ r : Fin (O.progCoins lam n) → Bool,
    ∃ S : Fin n → Bool, setOf lam n (O.genProg lam n r).1 = bits S ∧ wt S ≤ B lam n ∧
      ∀ x : Fin n → Bool, O.func lam n (O.genProg lam n r).1 x = true ↔ setAgree δ S x

/-- `(Π_EvObf, partOf)` is a **sparse-partition obfuscator at parameters `(p, τ, γ, b)`**
(STOC 2027 submission (manuscript sha256 52f4b606…a769709), Construction 6.1, p.37: "Let
`Π_EvObf_p` be the partition obfuscator at parameters `(p, τ, γ/2, b)`"): the object of the
conclusion of the published `SeededShannon.theorem_5_3` at these parameters, with minimum input
length `N_min`, supported on lengths divisible by `b`:
1. `Π_EvObf` is a distributional evasive obfuscator for `{f_P}`, `P` a partition of `[n]` into
   `b`-element blocks, `f_P(x) = 1 ⟺ x ∈ Ball_p(0^n) \ Bal_P(0^n; τ, γ)`;
2. the map `partOf` from sampling seeds to partition codes runs in time `poly(λ, n)`;
3. every returned seed `σ` determines a partition `P_σ` (`partOf(σ) = partCode P_σ`) with
   `f_σ = f_{P_σ}`. -/
def PartitionObf (p τ γ : ℝ) (b : ℕ) (Nmin : ℕ → ℕ) (O : EvObf)
    (partOf : ℕ → ℕ → List Bool → List Bool) : Prop :=
  PolyParam Nmin ∧
  O.IsEvObf Nmin (fun _ n => b ∣ n) (partFamily53 p τ γ b) ∧
  PolyTimeOn (ι := (z : {z : ℕ × ℕ // Nmin z.1 ≤ z.2 ∧ b ∣ z.2}) ×
      (Fin (O.progCoins z.1.1 z.1.2) → Bool))
    (fun i => [unary i.1.1.1, unary i.1.1.2, (O.genProg i.1.1.1 i.1.1.2 i.2).1])
    (fun i => partOf i.1.1.1 i.1.1.2 (O.genProg i.1.1.1 i.1.1.2 i.2).1) ∧
  ∀ lam n, Nmin lam ≤ n → b ∣ n → ∀ r : Fin (O.progCoins lam n) → Bool,
    ∃ P : Fin n → ℕ, IsBlockPartition b n P ∧
      partOf lam n (O.genProg lam n r).1 = partCode P ∧
      ∀ x : Fin n → Bool, O.func lam n (O.genProg lam n r).1 x = true ↔
        (ballP p (fun _ => false) x ∧ ¬ balP b τ γ P (fun _ => false) x)

end SeededShannon.Supplement



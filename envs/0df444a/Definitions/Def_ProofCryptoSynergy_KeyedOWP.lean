-- Prove2me | Definitions.Def_ProofCryptoSynergy_KeyedOWP
-- name    : ProofCryptoSynergy_KeyedOWP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:04:20.183323+00:00
-- url     : https://prove2.me/theorems/eb630aa3-e5c6-40ec-b7b2-2f592d1a920c
-- title:
--   Keyed, certifiable keyed and full-domain trapdoor one-way permutations
-- statement:
--   A **subexponentially secure keyed one-way permutation** with key length $\kappa(\eta)$ and domain $\{0,1\}^{d(\eta)}$ is a pair $(\mathrm{Gen},\mathrm{Eval})$ with:
--   1. $\mathrm{Gen}$ probabilistic polynomial-time, $\mathrm{Eval}$ deterministic polynomial-time;
--   2. $\mathrm{Gen}(1^\eta)\in\{0,1\}^{\kappa(\eta)}$;
--   3. for $k\in\mathrm{supp}(\mathrm{Gen}(1^\eta))$, $\mathrm{Eval}(1^\eta,k,-)$ is a permutation on $\{0,1\}^{d(\eta)}$;
--   4. for some $\delta>0$ and all large $\eta$, every circuit $C$ of size at most $2^{\eta^\delta}$ has
--   $$\Pr_{k\leftarrow\mathrm{Gen}(1^\eta),\,x\leftarrow\{0,1\}^{d(\eta)}}[C(k,\mathrm{Eval}(1^\eta,k,x))=x]\le 2^{-\eta^\delta}.$$
--   It is **certifiable** if a deterministic polynomial-time $\mathrm{Cert}$ has $\mathrm{Cert}(1^\eta,k)=1$ iff $\mathrm{Eval}(1^\eta,k,-)$ is a permutation. A **full-domain trapdoor** one-way permutation is a keyed one in which $\mathrm{Gen}$ also gives a trapdoor that allows polynomial-time inversion.
--
--   **Formalization Note** $d$ is polynomially bounded (p.14 and the proof of Proposition 20). Trapdoor permutations are used by the paper without definition.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definitions 18, 19, pp.21–22 (PDF 23–24); Lemma 15, p.21 (PDF 23)

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit
import Definitions.Def_LaconicBarrier_PolyTimeOn
import Definitions.Def_LaconicBarrier_coinAvg

open LaconicBarrier

namespace ProofCryptoSynergy

/-- The data of a keyed permutation: key length `κ(η)`, input domain `{0,1}^{d(η)}`, `s(η)` coins of `Gen`,
`Gen(1^η; r)` and `Eval(1^η, k, x)`. -/
structure KeyedOWP where
  /-- the key length -/
  kappa : ℕ → ℕ
  /-- the domain length -/
  d : ℕ → ℕ
  /-- the number of coins of `Gen` -/
  s : ℕ → ℕ
  /-- key generation -/
  gen : ℕ → List Bool → List Bool
  /-- evaluation -/
  eval : ℕ → List Bool → List Bool → List Bool

/-- `F` is a permutation on `{0,1}^d`. -/
def IsPermOn (d : ℕ) (F : List Bool → List Bool) : Prop :=
  Set.BijOn F {x | x.length = d} {x | x.length = d}

/-- `Pr_{k←Gen(1^η), x←{0,1}^{d(η)}}[C(k, Eval(1^η, k, x)) = x]`, for a multi-output circuit with `m` inputs reading
`k` followed by the image through `padIn m`. -/
noncomputable def KeyedOWP.invProb (W : KeyedOWP) (η : ℕ) {m : ℕ} (C : MCircuit m) : ℝ :=
  coinAvg (W.s η) fun r => coinAvg (W.d η) fun x =>
    if C.eval (padIn m (W.gen η (bits r) ++ W.eval η (W.gen η (bits r)) (bits x))) = bits x
    then 1 else 0

/-- A **subexponentially secure keyed (full-domain) one-way permutation** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 18, pp.21–22 (PDF 23–24)):
1. `Gen` runs in probabilistic polynomial time and `Eval` in deterministic polynomial time;
2. for all `η`, `Gen(1^η) ∈ {0,1}^{κ(η)}`;
3. for all `η` and `k ∈ supp(Gen(1^η))`, `Eval(1^η, k, −)` is a permutation on `{0,1}^{d(η)}`;
4. there is `δ > 0` such that for large `η`, every circuit `C` of size at most `2^{η^δ}` has
   `Pr[C(k, Eval(1^η, k, x)) = x] ≤ 2^{-η^δ}`.

**Formalization Note** `d` is polynomially bounded: Definition 18 does not say so, but p.14 has `x ∈ {0,1}^{poly(η)}` and the proof of
Proposition 20 says `n = poly(η)`. `|C|` is `MCircuit.size`, gates plus output wires. -/
def IsSubexpKeyedOWP (W : KeyedOWP) : Prop :=
  (∃ c : ℕ, ∀ η, W.s η ≤ (η + 2) ^ c) ∧
  (∃ c : ℕ, ∀ η, W.d η ≤ (η + 2) ^ c) ∧
  PolyTimeOn (ι := {i : ℕ × List Bool // i.2.length = W.s i.1})
    (fun i => [unary i.1.1, i.1.2]) (fun i => W.gen i.1.1 i.1.2) ∧
  PolyTimeOn (ι := ℕ × List Bool × List Bool)
    (fun i => [unary i.1, i.2.1, i.2.2]) (fun i => W.eval i.1 i.2.1 i.2.2) ∧
  (∀ (η : ℕ) (r : List Bool), r.length = W.s η → (W.gen η r).length = W.kappa η) ∧
  (∀ (η : ℕ) (r : List Bool), r.length = W.s η → IsPermOn (W.d η) (W.eval η (W.gen η r))) ∧
  ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ η : ℕ in Filter.atTop, ∀ (m : ℕ) (C : MCircuit m),
    (C.size : ℝ) ≤ (2 : ℝ) ^ ((η : ℝ) ^ δ) → W.invProb η C ≤ (2 : ℝ) ^ (-((η : ℝ) ^ δ))

/-- **There exists a subexponentially secure keyed OWP** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 39, assumption 1, p.34 (PDF 36)). -/
def SubexpKeyedOWPExists : Prop := ∃ W : KeyedOWP, IsSubexpKeyedOWP W

/-- A subexponentially secure keyed OWP `W` is **certifiable** by `cert` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 19, p.22 (PDF 24)): `cert` is deterministic
polynomial-time and `Cert(1^η, k) = 1` iff `Eval(1^η, k, −)` is a permutation. -/
def IsSubexpCertKeyedOWP (W : KeyedOWP) (cert : ℕ → List Bool → Bool) : Prop :=
  IsSubexpKeyedOWP W ∧
  PolyTimeOn (ι := ℕ × List Bool) (fun i => [unary i.1, i.2]) (fun i => [cert i.1 i.2]) ∧
  ∀ (η : ℕ) (k : List Bool), cert η k = true ↔ IsPermOn (W.d η) (W.eval η k)

/-- **There exists a subexponentially secure certifiable keyed OWP** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 39, p.34 (PDF 36)). -/
def SubexpCertKeyedOWPExists : Prop :=
  ∃ (W : KeyedOWP) (cert : ℕ → List Bool → Bool), IsSubexpCertKeyedOWP W cert

/-- The data of a full-domain trapdoor permutation: a keyed permutation whose `Gen` coins also give a trapdoor,
and an inverter using it. -/
structure TDPScheme extends KeyedOWP where
  /-- the trapdoor produced with the key, under the same coins -/
  td : ℕ → List Bool → List Bool
  /-- the inverter `Inv(1^η, t, y)` -/
  inv : ℕ → List Bool → List Bool → List Bool

/-- A **subexponentially secure full-domain trapdoor one-way permutation** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 15, p.21 (PDF 23); p.22 (PDF 24): "full-domain
trapdoor one-way permutations are a special case of keyed OWPs"): a keyed OWP with polynomial-time trapdoor generation and inversion,
`Inv(1^η, t, Eval(1^η, k, x)) = x` for every key `k` with trapdoor `t`.

**Formalization Note** The paper uses this without defining it; it is the standard definition in the format of Definition 18. -/
def IsSubexpTDP (W : TDPScheme) : Prop :=
  IsSubexpKeyedOWP W.toKeyedOWP ∧
  PolyTimeOn (ι := {i : ℕ × List Bool // i.2.length = W.s i.1})
    (fun i => [unary i.1.1, i.1.2]) (fun i => W.td i.1.1 i.1.2) ∧
  PolyTimeOn (ι := ℕ × List Bool × List Bool)
    (fun i => [unary i.1, i.2.1, i.2.2]) (fun i => W.inv i.1 i.2.1 i.2.2) ∧
  ∀ (η : ℕ) (r x : List Bool), r.length = W.s η → x.length = W.d η →
    W.inv η (W.td η r) (W.eval η (W.gen η r) x) = x

/-- **Subexponentially secure full-domain trapdoor OWPs exist** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 15, p.21 (PDF 23)). -/
def SubexpTDPExists : Prop := ∃ W : TDPScheme, IsSubexpTDP W

end ProofCryptoSynergy



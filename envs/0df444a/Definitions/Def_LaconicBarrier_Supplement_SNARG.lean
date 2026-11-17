-- Prove2me | Definitions.Def_LaconicBarrier_Supplement_SNARG
-- name    : LaconicBarrier_Supplement_SNARG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:29:46.268584+00:00
-- url     : https://prove2.me/theorems/da9ff277-6ff6-4808-8e9b-ed057a113b15
-- title:
--   SNARGs: syntax, polynomial time, completeness and the adaptive-soundness game
-- statement:
--   A **SNARG** for an NP relation $\mathcal R$ with language $L_{\mathcal R}$ is a triple $\Pi = (G, P, V)$:
--
--   1. $G(1^\lambda, 1^n) \to (\mathsf{pk}, \mathsf{vk})$, probabilistic: a public proving key and a private verification key; the setup may depend on $n = |x|$ but not on $x$;
--   2. $P(\mathsf{pk}, x, w) \to \pi$, probabilistic: the proof;
--   3. $V(\mathsf{vk}, x, \pi) \in \{0,1\}$, deterministic.
--
--   The three algorithms run in polynomial time (polynomially many coins and one machine each, within a polynomial of the input length). **Completeness** with witness bound $q$: for every polynomial $p$ there is a negligible $\kappa$ such that, for all $\lambda$, every $x$ with $|x| \le p(\lambda)$ and every $w$ with $|w| \le q(|x|)$ and $(x, w) \in \mathcal R$,
--   $$
--   \Pr\bigl[V(\mathsf{vk}, x, \pi) = 1 : (\mathsf{pk}, \mathsf{vk}) \leftarrow G(1^\lambda, 1^{|x|}),\ \pi \leftarrow P(\mathsf{pk}, x, w)\bigr] \ge 1 - \kappa(\lambda).
--   $$
--   The **adaptive-soundness game** $C_{1^n}$ samples $(\mathsf{pk}, \mathsf{vk}) \leftarrow G(1^\lambda, 1^n)$, sends $\mathsf{pk}$, receives $(x, \pi)$, and wins exactly when $|x| = n$, $x \notin L_{\mathcal R}$ and $V(\mathsf{vk}, x, \pi) = 1$; its baseline is $0$ and its index set is $\{1^n : n \in \mathbb N\}$. The check $x \notin L_{\mathcal R}$ need not be efficient.
--
--   These objects state Theorems 6.8, 6.10 and A.5, which concern adaptively sound SNARGs whose soundness has a black-box reduction to a falsifiable assumption.
--
--   **Formalization Note** "There is a negligible $\kappa$" is written as: for every $K > 0$, for all large $\lambda$, the acceptance probability is at least $1 - \lambda^{-K}$ on every admissible pair; for each $\lambda$ there are finitely many pairs, so the two forms are equivalent. The adversary's reply $(x, \pi)$ is one string, the injective tuple code of the published `QAdvFew.PoQOracle.tup`; a reply that is not such a code loses. The game is an instance of the published family of two-message games `LaconicBarrier.TwoMsg`.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.3 and Definition 4.7, pp.17–18

import Mathlib
import Definitions.Def_LaconicBarrier_PolyTimeOn
import Definitions.Def_LaconicBarrier_coinAvg
import Definitions.Def_LaconicBarrier_Lang
import Definitions.Def_LaconicBarrier_TwoMsg
import Definitions.Def_QAdvFew_PoQOracle_tup

namespace LaconicBarrier.Supplement

open KarpLiptonOM

/-- A **SNARG** `Π = (G, P, V)` for an NP relation (Jain, Mathialagan, Roy, *From Succinct
Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript
sha256 1af78662…), §4.1.3, p.17, "Syntax"):
1. `G(1^λ, 1ⁿ) → (pk, vk)`, probabilistic, with `gcoins λ n` coins: a public proving key and a
   private verification key ("The setup may depend on `n = |x|`, but not on `x`");
2. `P(pk, x, w) → π`, probabilistic, with `pcoins pk x w` coins;
3. `V(vk, x, π) ∈ {0, 1}`, deterministic.

**Formalization Note** Polynomial time is `SNARG.IsPPT`, completeness is `SNARG.Complete`, and
adaptive soundness is the game `SNARG.adaptiveSource`; the proof-length and proving-key-length
bounds `ℓ_P`, `ℓ_V` are hypotheses of the theorems that use them. -/
structure SNARG where
  /-- the number of coins of `G` at `(λ, n)` -/
  gcoins : ℕ → ℕ → ℕ
  /-- the setup `G(1^λ, 1ⁿ) = (pk, vk)` -/
  G : (lam n : ℕ) → (Fin (gcoins lam n) → Bool) → List Bool × List Bool
  /-- the number of coins of the prover -/
  pcoins : List Bool → List Bool → List Bool → ℕ
  /-- the prover `P(pk, x, w)` -/
  P : (pk x w : List Bool) → (Fin (pcoins pk x w) → Bool) → List Bool
  /-- the verifier `V(vk, x, π)` -/
  V : List Bool → List Bool → List Bool → Bool

/-- The three algorithms of the SNARG run in **polynomial time** (Jain, Mathialagan, Roy, STOC 2027
submission (manuscript sha256 1af78662…), §4.1.3, p.17: "a triple `Π = (G, P, V)` of polynomial-time
algorithms"): polynomially many coins, and one machine each for `G` (on `(1^λ, 1ⁿ, ρ)`), `P` (on
`(pk, x, w, ρ)`) and `V` (on `(vk, x, π)`), each within a polynomial of its input length. -/
def SNARG.IsPPT (S : SNARG) : Prop :=
  (∃ c : ℕ, ∀ lam n, S.gcoins lam n ≤ (lam + n + 2) ^ c) ∧
  (∃ c : ℕ, ∀ pk x w, S.pcoins pk x w ≤ (pk.length + x.length + w.length + 2) ^ c) ∧
  PolyTimeOn (ι := (lam : ℕ) × (n : ℕ) × (Fin (S.gcoins lam n) → Bool))
    (fun i => [unary i.1, unary i.2.1, bits i.2.2])
    (fun i => QAdvFew.PoQOracle.tup [(S.G i.1 i.2.1 i.2.2).1, (S.G i.1 i.2.1 i.2.2).2]) ∧
  PolyTimeOn (ι := (pk : List Bool) × (x : List Bool) × (w : List Bool) ×
      (Fin (S.pcoins pk x w) → Bool))
    (fun i => [i.1, i.2.1, i.2.2.1, bits i.2.2.2]) (fun i => S.P i.1 i.2.1 i.2.2.1 i.2.2.2) ∧
  PolyTimeOn (ι := List Bool × List Bool × List Bool) (fun i => [i.1, i.2.1, i.2.2])
    (fun i => [S.V i.1 i.2.1 i.2.2])

/-- The distribution of the honest proof `P(pk, x, w)` over the prover's coins. -/
noncomputable def SNARG.proverPMF (S : SNARG) (pk x w : List Bool) : PMF (List Bool) :=
  (PMF.uniformOfFintype (Fin (S.pcoins pk x w) → Bool)).map (S.P pk x w)

/-- `Pr[V(vk, x, π) = 1 : (pk, vk) ← G(1^λ, 1^{|x|}), π ← P(pk, x, w)]` (Jain, Mathialagan, Roy,
STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.7, p.17, Completeness). -/
noncomputable def SNARG.honestAcc (S : SNARG) (lam : ℕ) (x w : List Bool) : ℝ :=
  coinAvg (S.gcoins lam x.length) fun ρ =>
    coinAvg (S.pcoins (S.G lam x.length ρ).1 x w) fun ρ' =>
      if S.V (S.G lam x.length ρ).2 x (S.P (S.G lam x.length ρ).1 x w ρ') then 1 else 0

/-- **Completeness** of a SNARG for the relation `R` with witness bound `q` (Jain, Mathialagan, Roy,
STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.7, p.17: "For every polynomial `p`,
there exists a negligible function `κ` such that, for every `λ, n, m ∈ ℕ` with `n ≤ p(λ)` and
`m ≤ q(n)`, and every `x ∈ {0,1}ⁿ`, `w ∈ {0,1}^m` with `(x, w) ∈ R`, `Pr[…] ≥ 1 − κ(λ)`").

**Formalization Note** "There is a negligible `κ` with `Pr ≥ 1 − κ(λ)`" is written: for every
`K > 0`, for all large `λ`, the acceptance probability is at least `1 − λ^{−K}` on every such pair.
The two are equivalent because for each `λ` there are finitely many pairs, so the worst error is a
function of `λ`. -/
def SNARG.Complete (S : SNARG) (Rel : List Bool → List Bool → Prop) (q : Polynomial ℕ) : Prop :=
  ∀ p : Polynomial ℕ, ∀ K : ℕ, 0 < K → ∀ᶠ lam : ℕ in Filter.atTop, ∀ x w : List Bool,
    x.length ≤ p.eval lam → w.length ≤ q.eval x.length → Rel x w →
      1 - (((lam : ℝ) ^ K))⁻¹ ≤ S.honestAcc lam x w

/-- The index set `X = {1ⁿ : n ∈ ℕ}` of the adaptive-soundness games (Jain, Mathialagan, Roy, STOC
2027 submission (manuscript sha256 1af78662…), §4.1.3, p.18). -/
def unaryIdx : Set (List Bool) := Set.range unary

open Classical in
/-- The **adaptive-soundness game** of a SNARG as a family of two-message games with index `1ⁿ`
(Jain, Mathialagan, Roy, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.3, p.18: "Let
`C_{1ⁿ}` sample `(pk, vk) ← G(1^λ, 1ⁿ)`, send `pk`, receive `(x, π)`, and output `win` precisely
when `|x| = n`, `x ∉ L_R`, and `V(vk, x, π) = 1`"; family `{(C_{1ⁿ}, 0)}_{1ⁿ ∈ X}`). On an index
`u` the challenger uses `n = |u|`; the index set is `unaryIdx`.

**Formalization Note** The response `(x, π)` is one string, the tuple code
`tup [x, π]` (`QAdvFew.PoQOracle.tup`, injective); a response that is not such a code loses. The
check `x ∉ L_R` need not be efficient ("this check need not be efficient", p.18). Baseline `0`. -/
noncomputable def SNARG.adaptiveSource (S : SNARG) (Rel : List Bool → List Bool → Prop) :
    TwoMsg where
  coins lam u := S.gcoins lam u.length
  chal lam u ρ := (S.G lam u.length ρ).1
  wins lam u ρ a := decide (∃ x π : List Bool, a = QAdvFew.PoQOracle.tup [x, π] ∧
    x.length = u.length ∧ x ∉ Lang Rel ∧ S.V (S.G lam u.length ρ).2 x π = true)
  c₀ := 0
  c₀_nonneg := le_refl 0
  c₀_lt_one := zero_lt_one

end LaconicBarrier.Supplement



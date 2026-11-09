-- Prove2me | Definitions.Def_PrivPCP_PrivPCPSys
-- name    : PrivPCP_PrivPCPSys
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:16.111724+00:00
-- url     : https://prove2.me/theorems/eb959800-bfe8-4d71-b21e-dc401c3e865c
-- title:
--   Private-PCP systems for Circuit-SAT and their clauses
-- statement:
--   A **private-PCP system** with proof length $M(n)$ and alphabet size $q(n)$ consists of
--
--   1. a randomized prover $\Pi$ that maps every circuit $\Phi$ of size $n$ and **every** assignment $w\in\{0,1\}^m$ (satisfying or not) to a probability law $\Pi(\Phi,w)$ on proofs $\pi\in\Sigma^M$, $\Sigma=\{0,\dots,q(n)-1\}$;
--   2. a deterministic machine $S$ with coin length $\sigma$ and clock $\theta$ that samples $\Pi(\Phi,w)$;
--   3. a deterministic oracle machine $V$ (the verifier) with coin length $\rho_V$ and clock $\tau_V$ that reads the proof through an oracle.
--
--   The clauses of Definition 8.2 are:
--
--   - **Samplable**: $\sigma,\theta$ are polynomially bounded and, for every $\Phi,w$, there is a map $g$ from coins to proofs such that the image of the uniform law on the coins under $g$ is exactly $\Pi(\Phi,w)$, and on every coin value $c$ the machine $S$, given $(\Phi,w,c)$, halts within $\theta$ steps with the code of $g(c)$ as output. The coins are $\sigma$ uniform bits together with $\sigma$ uniform elements of $\Sigma$ (the honest prover samples uniform polynomials over $\mathbb F_q$, which bit coins cannot do exactly for odd $q$; a field-coin sampler is simulated exactly by a Las Vegas bit sampler in expected polynomial time).
--   - **Efficient** with query bound $Q$: $\rho_V,\tau_V$ are polynomially bounded and, for every circuit, coin string and proof, $V$ halts within $\tau_V$ steps having read at most $Q(n)$ distinct proof positions.
--   - **Nonadaptive**: under fixed coins, the set $Q(r)$ of positions read does not depend on the proof.
--   - **Complete** (perfect completeness): if $\Phi(w)=1$, $V$ accepts every proof in the support of $\Pi(\Phi,w)$ on every coin string.
--   - **Sound** with error $s$: for every $\Phi\notin\mathrm{CircuitSAT}$ and every $\pi\in\Sigma^M$, $\Pr_V[V^\pi(\Phi)=1]\le s(n)$.
--   - The **verifier-induced measure** on positions: sample the coins $r$, then a uniformly random position among those queried,
--   $$\mu_{V,\Phi}(T)=2^{-\rho_V}\sum_{r}\frac{|T\cap Q(r)|}{|Q(r)|}.$$
--   - **$\nu$-private**: for every circuit $\Phi$, all $w,w'\in\{0,1\}^m$ and every set $T$ of positions with $\mu_{V,\Phi}(T)<\nu(n)$,
--   $$\Pi(\Phi,w)|_T\overset{d}{=}\Pi(\Phi,w')|_T.$$
--
--   Privacy compares the honest proofs of any two assignments, satisfying or not; it is stronger than zero knowledge, which concerns satisfying assignments only.
--
--   **Formalization Note** Machines are the published oracle Turing machines; the query log, the proof oracle (positions and symbol bits in binary) and the acceptance probability are the published PCP bookkeeping. $M$ and $q$ are functions of the size $n$ alone. A coin string reading no position contributes $0$ to $\mu$ (the paper's verifier always reads one), and the positions are those read against a reference proof $\pi_0$; for a nonadaptive verifier $\mu$ does not depend on $\pi_0$.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Definition 8.2, p.46 (PDF p.48); §6.3, the measure µ, p.39 (PDF p.41)

import Mathlib
import Definitions.Def_PrivPCP_Circuit
import Definitions.Def_ZKSheafPCP_queryLog
import Definitions.Def_ZKSheafPCP_IsPolynomial

open QAlgorithms.Complexity QAdvFew.PoQOracle ZKSheafPCP

namespace PrivPCP

open Classical

/-- A **private-PCP system for Circuit-SAT** with proof length `M` and alphabet size `q` (Bafna, Vyas, *Private
PCPs from Product Expansion*, STOC 2027 submission manuscript (sha256 c2cac1e0…), Definition 8.2, p.46): the
randomized prover `P`, mapping every circuit `Φ` and **every** assignment `w ∈ {0,1}^m` (satisfying or not) to
a law `Π(Φ, w)` on `Σ^M`, `Σ = Fin (q n)`, `n = size Φ`; a machine `S` sampling `Π(Φ, w)` from `σ` uniform bits and `σ` uniform elements of `Σ`
within `θ` steps; and the oracle verifier `V` with coin length `ρV` and clock `τV`.

**Formalization Note** `M` and `q` are functions of the size `n` alone, one system for all circuits. The coin
lengths and clocks are functions of the length of the machine's input. -/
structure PrivPCPSys (M q : ℕ → ℕ) where
  /-- the honest prover: the law of the proof `Π(Φ, w)` -/
  P : ∀ Φ : Circuit, (Fin Φ.1 → ZMod 2) → PMF (Fin (M Φ.size) → Fin (q Φ.size))
  /-- the prover's sampling machine -/
  S : OTM
  /-- the sampler's coin length (bits and field elements) -/
  σ : ℕ → ℕ
  /-- the sampler's clock -/
  θ : ℕ → ℕ
  /-- the verifier -/
  V : OTM
  /-- the verifier's coin length -/
  ρV : ℕ → ℕ
  /-- the verifier's clock -/
  τV : ℕ → ℕ

/-- The code of a proof `π ∈ Σ^ℓ`: its symbols in binary, as a tuple. -/
def proofCode {ℓ a : ℕ} (π : Fin ℓ → Fin a) : Str :=
  tup ((List.finRange ℓ).map fun i => binN (π i).val)

/-- An assignment `w ∈ {0,1}^m` as a bit string. -/
def assignStr {m : ℕ} (w : Fin m → ZMod 2) : Str := List.ofFn fun i => decide (w i = 1)

namespace PrivPCPSys

variable {M q : ℕ → ℕ} (Sys : PrivPCPSys M q)

/-- The sampler's input `(Φ, w)`. -/
def samplerInput (Φ : Circuit) (w : Fin Φ.1 → ZMod 2) : Str := tup [Φ.code, assignStr w]

/-- The sampler's coin space on `(Φ, w)`: `σ` uniform bits and `σ` uniform field elements of `Σ = Fin (q n)`. -/
abbrev SamplerCoins (Φ : Circuit) (w : Fin Φ.1 → ZMod 2) : Type :=
  (Fin (Sys.σ (samplerInput Φ w).length) → Bool) × (Fin (Sys.σ (samplerInput Φ w).length) → Fin (q Φ.size))

/-- **Polynomial-time samplability** of `Π(Φ, w)` (Definition 8.2): `σ` and `θ` are polynomially bounded and,
for every circuit `Φ` and every assignment `w`, there is a map `g` from coins to proofs whose image of the
uniform law on the coins is exactly `Π(Φ, w)`, and on every coin value `c = (b, u)` the machine `S`, run on
`(Φ, w, b, u)`, halts within `θ(|(Φ, w)|)` steps with the code of the proof `g(c)` on its work tape.

**Formalization Note** The coins are uniform bits `b` together with uniform field elements `u ∈ 𝔽_q^σ`
(written in binary, like proof symbols). The honest prover of the paper samples uniform polynomials and
uniform certificates over `𝔽_q` (§5.2, p.28; §6.2, p.36), and exact privacy needs these laws exactly; for odd
`q` no fixed number of bit coins gives an exactly uniform element of `𝔽_q`. A sampler with field coins is
simulated exactly by a Las Vegas bit sampler in expected polynomial time. The law clause is a counting identity:
`Π(Φ, w)(π)` is the fraction of coin values that `g` maps to `π` (if the coin space were empty every mass would
be `0`, impossible for a probability law). -/
def Samplable : Prop :=
  PolyBdd Sys.σ ∧ PolyBdd Sys.θ ∧
  ∀ (Φ : Circuit) (w : Fin Φ.1 → ZMod 2),
    ∃ g : Sys.SamplerCoins Φ w → (Fin (M Φ.size) → Fin (q Φ.size)),
      (∀ π, Sys.P Φ w π =
        (Fintype.card {c // g c = π} : ENNReal) / (Fintype.card (Sys.SamplerCoins Φ w) : ENNReal)) ∧
      ∀ c : Sys.SamplerCoins Φ w,
        Sys.S.result (fun _ => false) (tup [Φ.code, assignStr w, coinStr c.1, proofCode c.2])
            (Sys.θ (samplerInput Φ w).length) ≠ none ∧
        Sys.S.output (fun _ => false) (tup [Φ.code, assignStr w, coinStr c.1, proofCode c.2])
            (Sys.θ (samplerInput Φ w).length) = proofCode (g c)

/-- The set `Q(r)` of proof positions the verifier reads on circuit `Φ`, coins `r` and proof `π`. -/
noncomputable def queried (Φ : Circuit) (r : Fin (Sys.ρV Φ.code.length) → Bool)
    (π : Fin (M Φ.size) → Fin (q Φ.size)) : Set (Fin (M Φ.size)) :=
  queriedPositions (M Φ.size) (queryLog Sys.V (proofOracle π) (tup [Φ.code, coinStr r]) (Sys.τV Φ.code.length))

/-- The verifier is **probabilistic polynomial time** and makes at most `Q(n)` queries: `ρV` and `τV` are
polynomially bounded and, on every circuit, coin string and proof, `V` halts within `τV(|Φ|)` steps having read
at most `Q(size Φ)` distinct proof positions. -/
def Efficient (Q : ℕ → ℝ) : Prop :=
  PolyBdd Sys.ρV ∧ PolyBdd Sys.τV ∧
  ∀ (Φ : Circuit) (r : Fin (Sys.ρV Φ.code.length) → Bool) (π : Fin (M Φ.size) → Fin (q Φ.size)),
    Sys.V.result (proofOracle π) (tup [Φ.code, coinStr r]) (Sys.τV Φ.code.length) ≠ none ∧
    ((Sys.queried Φ r π).ncard : ℝ) ≤ Q Φ.size

/-- The verifier is **nonadaptive**: under fixed coins, the set of positions it reads does not depend on the
proof. -/
def IsNonadaptive : Prop :=
  ∀ (Φ : Circuit) (r : Fin (Sys.ρV Φ.code.length) → Bool) (π π' : Fin (M Φ.size) → Fin (q Φ.size)),
    Sys.queried Φ r π = Sys.queried Φ r π'

/-- **Perfect completeness** (Definition 8.2): if `Φ(w) = 1`, the verifier accepts every proof in the support
of `Π(Φ, w)` on every coin string. -/
def Complete : Prop :=
  ∀ (Φ : Circuit) (w : Fin Φ.1 → ZMod 2), Φ.eval w = 1 →
    ∀ π ∈ (Sys.P Φ w).support, ∀ r : Fin (Sys.ρV Φ.code.length) → Bool,
      Sys.V.result (proofOracle π) (tup [Φ.code, coinStr r]) (Sys.τV Φ.code.length) = some true

/-- **Soundness** `s` (Definition 8.2): for every `Φ ∉ CircuitSAT` and every `π ∈ Σ^M`,
`Pr_V[V^π(Φ) = 1] ≤ s(size Φ)`. -/
def Sound (s : ℕ → ℝ) : Prop :=
  ∀ Φ ∉ CircuitSAT, ∀ π : Fin (M Φ.size) → Fin (q Φ.size),
    acceptProb Sys.V (proofOracle π) Φ.code (Sys.ρV Φ.code.length) (Sys.τV Φ.code.length) ≤ s Φ.size

/-- The **verifier-induced measure** `µ_{V,Φ}` (Definition 8.2; §6.3, p.39): sample the verifier's coins `r`
uniformly, then a uniformly random position among the set `Q(r)` it queries,
`µ(T) = 2^{−ρV} ∑_r |T ∩ Q(r)| / |Q(r)|`. The positions are those read against the proof `π₀`.

**Formalization Note** A coin string that reads no position contributes `0` (Lean's `x / 0 = 0`); the paper's
verifier always reads at least one position (§6.3: "the nonempty set of transcript coordinates queried"). For a
nonadaptive verifier `µ` does not depend on `π₀`. -/
noncomputable def mu (Φ : Circuit) (π₀ : Fin (M Φ.size) → Fin (q Φ.size)) (T : Set (Fin (M Φ.size))) : ℝ :=
  (∑ r : Fin (Sys.ρV Φ.code.length) → Bool,
      ((T ∩ Sys.queried Φ r π₀).ncard : ℝ) / (Sys.queried Φ r π₀).ncard) / 2 ^ Sys.ρV Φ.code.length

/-- **`ν`-privacy** (Definition 8.2): for every circuit `Φ`, all assignments `w, w′` (satisfying or not) and
every set `T` of positions with `µ_{V,Φ}(T) < ν(size Φ)`, the marginal laws of `Π(Φ, w)` and `Π(Φ, w′)` on `T`
are equal. -/
def Private (ν : ℕ → ℝ) : Prop :=
  ∀ (Φ : Circuit) (w w' : Fin Φ.1 → ZMod 2) (π₀ : Fin (M Φ.size) → Fin (q Φ.size))
    (T : Set (Fin (M Φ.size))), Sys.mu Φ π₀ T < ν Φ.size →
    (Sys.P Φ w).map (fun π (i : T) => π i) = (Sys.P Φ w').map (fun π (i : T) => π i)

end PrivPCPSys

end PrivPCP



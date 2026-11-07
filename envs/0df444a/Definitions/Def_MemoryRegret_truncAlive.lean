-- Prove2me | Definitions.Def_MemoryRegret_truncAlive
-- name    : MemoryRegret_truncAlive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:45.409863+00:00
-- url     : https://prove2.me/theorems/ac4967f2-ce23-4888-8dac-78f6e4a8a181
-- title:
--   The truncated path $\mathcal T$ and the event "reaches a significant vertex"
-- statement:
--   Let $w$ be the joint law of the hidden index $i$ and the samples, and let $\ell'=\ell/6$, $r'=\min(r/2,k/4,\ell/5)$ as in eq. (10). The **truncated path** $\mathcal T$ is defined by induction on layers. Having defined $\mathcal T$ up to layer $i$, for a vertex $v$ in layer $i$ let $E_v^\dagger$ be the event that $\mathcal T$ reaches $v$ and $\mathbb P^\dagger_{h|v}$ the law of $h$ given $E_v^\dagger$. The path, having reached $v$, stops if at least one of the following holds:
--
--   1. $v$ is **significant**: $\|\mathbb P^\dagger_{h|v}\|_2>2^{\ell'}/|H|$;
--   2. $h\in\mathrm{Sig}(v)$: $\mathbb P^\dagger_{h|v}(h)>2^{2\ell'+2r'}/|H|$;
--   3. $x_{i+1}\in\mathrm{Bad}(v)$: $\bigl|\mathbb E_{h'\sim\mathbb P^\dagger_{h|v}}[(-1)^{h'(x_{i+1})}]\bigr|\ge2^{-r}$;
--   4. $b_{i+1}\in\mathrm{BadBlock}$;
--   5. $v$ is a leaf.
--
--   Otherwise it follows the edge labeled $(x_{i+1},b_{i+1})$. The event **$\mathcal T$ reaches a significant vertex** is the event that for some layer $\mathcal T$ reaches a vertex $v$ of that layer which is significant. The same posterior construction with an arbitrary event $\mathcal E$ gives the law $\mathbb P^{\mathcal E}_{h|v}$ of Proposition 5.
--
--   **Formalization Note** `truncAlive` is the set of outcomes on which $\mathcal T$ has not stopped at the layers before $i$; with `Reaches` it is $E_v^\dagger$. Posteriors at vertices of probability $0$ are $0/0=0$ in Lean; such vertices are never reached, so no stopping decision depends on that value. Samples are 0-based: the edge out of layer $i$ reads sample $i$.
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), §3.3, eq. (10), pp.17–18

import Mathlib
import Definitions.Def_MemoryRegret_IsProbVec
import Definitions.Def_MemoryRegret_sgn
import Definitions.Def_MemoryRegret_IsL2Extractor
import Definitions.Def_MemoryRegret_berBlock
import Definitions.Def_MemoryRegret_streamD1
import Definitions.Def_MemoryRegret_BranchingProgram

namespace MemoryRegret

variable {X ι S : Type} [Fintype X] [Fintype ι] {m τ : ℕ}

/-- The posterior of the hidden hypothesis at the vertex `(i, v)` given an event `E`:
`P_{h|E ∧ reach (i,v)}(h′) = Pr[h = h′ ∧ E ∧ reach (i,v)] / Pr[E ∧ reach (i,v)]` under the
joint weight `w` on `ι × streams`. With `E` the truncated-path event this is `P†_{h|v}`
(p.17); with `E` the event of Proposition 5 it is `P^E_{h|v}` (p.10). -/
noncomputable def postAt (w : ι × (Fin τ → X × (Fin m → Bool)) → ℝ)
    (B : BranchingProgram S (X × (Fin m → Bool)) τ) (E : Set (ι × (Fin τ → X × (Fin m → Bool))))
    (i : ℕ) (v : S) (h' : ι) : ℝ :=
  wprob w (fun p => p ∈ E ∧ B.Reaches p.2 i v ∧ p.1 = h') /
    wprob w (fun p => p ∈ E ∧ B.Reaches p.2 i v)

/-- The four stopping rules of the truncated path at the vertex `v = stateAt i` it has reached
in layer `i`, plus "v is a leaf" (§3.3, pp.17–18), with `ℓ′ = ℓ/6` and
`r′ = min(r/2, k/4, ℓ/5)` (eq. (10)), `P = P†_{h|v}` computed from the truncated path up to
layer `i` (the set `alive`): `v` is a leaf; `v` is significant (`‖P‖₂ > 2^{ℓ′}/|H|`);
`h ∈ Sig(v)` (`P(h) > 2^{2ℓ′+2r′}/|H|`); `x_{i+1} ∈ Bad(v)`
(`|E_{h′∼P}[(−1)^{h′(x_{i+1})}]| ≥ 2^{−r}`); or `b_{i+1} ∈ BadBlock`. -/
def truncStops (w : ι × (Fin τ → X × (Fin m → Bool)) → ℝ) (hyp : ι → X → Bool)
    (B : BranchingProgram S (X × (Fin m → Bool)) τ) (k ℓ r : ℝ)
    (alive : Set (ι × (Fin τ → X × (Fin m → Bool)))) (i : ℕ)
    (p : ι × (Fin τ → X × (Fin m → Bool))) : Prop :=
  B.IsLeafVertex i (B.stateAt p.2 i) ∨
  (2 : ℝ) ^ (ℓ / 6) / Fintype.card ι < unifNorm2 (postAt w B alive i (B.stateAt p.2 i)) ∨
  (2 : ℝ) ^ (2 * (ℓ / 6) + 2 * min (r / 2) (min (k / 4) (ℓ / 5))) / Fintype.card ι <
    postAt w B alive i (B.stateAt p.2 i) p.1 ∨
  ∃ h : i < τ,
    (2 : ℝ) ^ (-r) ≤ |∑ h', postAt w B alive i (B.stateAt p.2 i) h' * sgn (hyp h' (p.2 ⟨i, h⟩).1)| ∨
    (p.2 ⟨i, h⟩).2 ∈ BadBlock m r

/-- **The truncated path (§3.3, pp.17–18).**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
§3.3, pp.17–18: "We will define the truncated-path, 𝒯, to be the same as the computation-path
of B, except that it sometimes stops before reaching a leaf. … Formally, 𝒯 (and hence event ℰ)
is defined by induction on the layers of the branching program B." The path, having reached
`v` in layer `i`, stops if (1) `v` is significant, (2) `h ∈ Sig(v)`, (3) `x_{i+1} ∈ Bad(v)`,
(4) `b_{i+1} ∈ BadBlock`, or (5) `v` is a leaf; otherwise it follows the edge labeled
`(x_{i+1}, b_{i+1})`.

`truncAlive w hyp B k ℓ r i` is the set of outcomes `(h, stream)` for which the truncated path
has not stopped at any of the layers `0, …, i − 1`; together with `B.Reaches stream i v` it is
the event `E†_v` that the truncated path reaches `(i, v)`. The stopping rules at layer `i` use
`P†_{h|v}` computed from `truncAlive … i` (`truncStops`), which is the paper's induction.

**Formalization Note.** `w` is the joint weight of the hidden hypothesis and the samples (in
Lemma 3.4, `jointLaw µ hyp ε`: `h` uniform on `ι`, samples i.i.d. `D_h`). The parameters are
those of eq. (10), `ℓ′ = ℓ/6`, `r′ = min(r/2, k/4, ℓ/5)`, written out. Norms are with respect
to the uniform distribution on `ι`. Posteriors at vertices the truncated path reaches with
probability `0` are `0/0 = 0` in Lean; those vertices are never reached, so no stopping decision
depends on that value. Samples are 0-based: the edge out of layer `i` reads sample `i`. -/
def truncAlive (w : ι × (Fin τ → X × (Fin m → Bool)) → ℝ) (hyp : ι → X → Bool)
    (B : BranchingProgram S (X × (Fin m → Bool)) τ) (k ℓ r : ℝ) :
    ℕ → Set (ι × (Fin τ → X × (Fin m → Bool)))
  | 0 => Set.univ
  | i + 1 => {p | p ∈ truncAlive w hyp B k ℓ r i ∧
      ¬ truncStops w hyp B k ℓ r (truncAlive w hyp B k ℓ r i) i p}

/-- The event "𝒯 reaches a significant vertex" (Lemma 3.4, p.18): for some layer `i ≤ τ`, the
truncated path reaches the vertex `v = stateAt i` and `‖P†_{h|v}‖₂ > 2^{ℓ′}/|H|`. -/
def reachesSignificant (w : ι × (Fin τ → X × (Fin m → Bool)) → ℝ) (hyp : ι → X → Bool)
    (B : BranchingProgram S (X × (Fin m → Bool)) τ) (k ℓ r : ℝ) :
    Set (ι × (Fin τ → X × (Fin m → Bool))) :=
  {p | ∃ i ≤ τ, p ∈ truncAlive w hyp B k ℓ r i ∧ B.Reaches p.2 i (B.stateAt p.2 i) ∧
    (2 : ℝ) ^ (ℓ / 6) / Fintype.card ι <
      unifNorm2 (postAt w B (truncAlive w hyp B k ℓ r i) i (B.stateAt p.2 i))}

end MemoryRegret



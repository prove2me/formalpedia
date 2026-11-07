-- Prove2me | Definitions.Def_StretchDepth_Qset
-- name    : StretchDepth_Qset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:02.671439+00:00
-- url     : https://prove2.me/theorems/1861935a-b005-4e40-b29e-f695a8f80743
-- title:
--   The witness choice and the set $Q$
-- statement:
--   Let $\rho^+$ be a partial assignment and $T^+=T_{\rho^+}$. A **witness choice** assigns to $(\rho,y)$ a pair $(x,F)$ with $F\supseteq\rho$ and $H^F(x)=y$ whenever $T_\rho(y)=1$.
--
--   Given a deterministic procedure $t$ (the reduction on a fixed challenge), the function $G$ and the set $S^+$, with $\rho^+=G|_{\overline{S^+}}$, the set $Q\subseteq\{0,1\}^n$ contains:
--
--   1. every input at which $G$ is queried in the execution of $t$ with oracles $(G,T^+)$;
--   2. for each $y$ on which this execution queries $T^+$ and receives $T^+(y)=1$, every input at which $F$ is queried in the execution $H^F(x)$, where $(x,F)$ is the chosen witness for $(\rho^+,y)$.
--
--   It is the set of positions at which replanting $G$ could change the execution, and so it controls the correlated experiment of the proof of Theorem 1.
--
--   **Formalization Note** Any function of $(\rho,y)$ valid where $T_\rho(y)=1$ is allowed; the source's canonical choice is one such function.
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), proof of Theorem 1, p.20

import Definitions.Def_StretchDepth_IsPRGReduction
import Definitions.Def_StretchDepth_testOf

namespace StretchDepth

open QAlgorithms

variable {n N m M : ℕ}

/-- The queries made along the path a decision tree follows under the oracle `x`, in order. -/
def pathQueries {ι κ α : Type*} : DecisionTree ι κ α → (ι → κ) → List ι
  | .leaf _, _ => []
  | .node i next, x => i :: pathQueries (next (x i)) x

/-- Witness choice, proof of Theorem 1, p.20: "we choose some x ∈ {0, 1}m and some F ⊇ ρ+ such that
HF (x) = y ... choose these x, F canonically depending only on ρ+, y".

**Formalization Note.** Any function of `(ρ, y)` valid wherever `T_ρ(y) = 1`; the page's canonical
choice is one such function. -/
def IsWitness (H : Bits m → RoundTree n N M)
    (wit : PartialAssign n N → Bits M → Bits m × (Bits n → Bits N)) : Prop :=
  ∀ ρ y, testOf H ρ y = true →
    Extends (wit ρ y).2 ρ ∧ run (wit ρ y).2 (H (wit ρ y).1) = y

/-- **The set `Q`.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), proof of Theorem 1, p.20: "To define Q, we first include every input at which G
is queried in the execution RG,T +(z). In addition, for each y on which this execution queries T +
and receives the answer T +(y) = 1, we choose some x ∈ {0, 1}m and some F ⊇ ρ+ such that HF (x) = y
and include in Q all inputs at which F is queried in the execution HF (x)".

Here `t` is the deterministic procedure `R(z)`, `Splus` is `S⁺`, `ρ⁺ = freeOn G Splus` and
`T⁺ = testOf H ρ⁺`. -/
noncomputable def Qset (H : Bits m → RoundTree n N M)
    (wit : PartialAssign n N → Bits M → Bits m × (Bits n → Bits N)) (t : QProc n N M)
    (G : Bits n → Bits N) (Splus : Finset (Bits n)) : Finset (Bits n) :=
  (pathQueries t (oracle G (testOf H (freeOn G Splus)))).toFinset.biUnion fun q =>
    match q with
    | Sum.inl w => {w}
    | Sum.inr y =>
        if testOf H (freeOn G Splus) y = true then
          (queriesOf (wit (freeOn G Splus) y).2 (H (wit (freeOn G Splus) y).1)).flatten.toFinset
        else ∅

end StretchDepth



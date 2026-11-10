-- Prove2me | Definitions.Def_VAS5Reach_IsTAThreshold
-- name    : VAS5Reach_IsTAThreshold
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:28:43.596192+00:00
-- url     : https://prove2.me/theorems/f01deec4-a4cb-466a-99b9-67de4e0936f0
-- title:
--   Generalized transformation areas and transformation-area thresholds
-- statement:
--   Let $V$ be a VAS with transition set $T$ and $[\![V]\!]_{I,B}$ its $B$-encoding. Configurations $p(x)$ of $[\![V]\!]_{I,B}$ are identified with configurations of $V$ by restoring the encoded values, and Parikh images of its paths count their underlying transitions in $T$. A set $A \subseteq [0, B]^I \times \mathbb N^{[d]\setminus I}$ is a **generalized transformation area** for $[\![V]\!]_{I,B}$ (Definition 4.1) if for every $s, t \in A$ and every $\mathbb Z$-run $s \xrightarrow{\pi}_{\mathbb Z} t$ in $[\![V]\!]_{I,B}$ there is a run $s \xrightarrow{\rho} t$ in $V$ with $\psi_\rho = \psi_\pi$. A number $C$ is a **transformation-area threshold** for $[\![V]\!]_{I,B}$ if
--   $$
--   \mathcal G_C = [0, B]^I \times \{x \in \mathbb N^{[d]\setminus I} : x \ge C \cdot \mathbf 1\}
--   $$
--   is a generalized transformation area (`GC`, `IsTAThreshold`).
--
--   **Formalization Note** The paper's $I$ is the first two coordinates (w.l.o.g.); here $I$ is any set of coordinates.
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), §4, Definition 4.1 and the definition of a transformation-area threshold, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_VAS5Reach_IsVASRun
import Definitions.Def_VAS5Reach_VASS_IsRun
import Definitions.Def_VAS5Reach_encode

namespace VAS5Reach

variable {ι : Type}

/-- Definition 4.1: a set `A ⊆ [0, B]^I × ℕ^{[d]∖I}` of configurations of the `B`-encoding
`[[V]]_{I,B}` of a VAS `V` with transition set `T` is a generalized transformation area for
`[[V]]_{I,B}` if for every `s, t ∈ A` and every `ℤ`-run `s −π→_Z t` in `[[V]]_{I,B}` there is a run
`s −ρ→ t` in `V` with `ψ_ρ = ψ_π`, where configurations of `[[V]]_{I,B}` are identified with
configurations of `V` by restoring the encoded counter values (`decode`), and `ψ_π` counts the
underlying VAS transitions of `π` (`underlying`).

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), §4, printed p. 17
(PDF p. 19): "Let V be a (d + 2)-VAS with transition set T and [[V]]_B its B-encoding. We identify
each configuration p(x) of [[V]]_B with (p, x) ∈ N^{d+2} in V. Throughout this section, Parikh images
of paths in [[V]]_B count their underlying transitions in T. Definition 4.1. A set
A ⊆ [0, B]^2 × N^d is a generalized transformation area for [[V]]_B if for every s, t ∈ A and every
Z-run s −π→Z t in [[V]]_B, there is a run s −ρ→ t in V with ψρ = ψπ."

**Formalization Note** The encoded coordinates form an arbitrary `I : Finset ι` (the paper takes
`I` to be the first two coordinates, w.l.o.g.); the VAS is the one-state VASS `VASS.ofVAS T`, so a
state of the encoding is `((), u)` with `u ∈ [0, B]^I`. The inclusion `A ⊆ [0, B]^I × ℕ^{[d]∖I}`
is the first conjunct. -/
def IsGenTransArea (T : Finset (ι → ℤ)) (I : Finset ι) (B : ℕ)
    (A : Set ((Unit × (I → ℕ)) × ({i // i ∉ I} → ℕ))) : Prop :=
  (∀ a ∈ A, a.1.2 ∈ box I B) ∧
  ∀ s ∈ A, ∀ t ∈ A, ∀ π,
    (encode (VASS.ofVAS T) I B).IsZRun s.1 (fun j => (s.2 j : ℤ)) π t.1 (fun j => (t.2 j : ℤ)) →
    ∃ ρ, IsVASRun T (decode I s.1.2 s.2) ρ (decode I t.1.2 t.2) ∧
      parikh ρ = parikh (π.map (underlying I))

/-- `G_C = [0, B]^I × {x ∈ ℕ^{[d]∖I} : x ≥ C·1}`. -/
def GC (I : Finset ι) (B C : ℕ) : Set ((Unit × (I → ℕ)) × ({i // i ∉ I} → ℕ)) :=
  {a | a.1.2 ∈ box I B ∧ ∀ j, C ≤ a.2 j}

/-- `C` is a transformation-area threshold for `[[V]]_{I,B}` if
`G_C = [0, B]^I × {x ∈ ℕ^{[d]∖I} : x ≥ C·1}` is a generalized transformation area for `[[V]]_{I,B}`.

Source: arXiv:2610.40012 (held version, sha256 a74d76f9…), §4, printed p. 17 (PDF p. 19):
"Recall that C is a transformation-area threshold for [[V]]_B if G_C = [0, B]^2 × {x ∈ N^d : x ≥ C · 1}
is a generalized transformation area for [[V]]_B." -/
def IsTAThreshold (T : Finset (ι → ℤ)) (I : Finset ι) (B C : ℕ) : Prop :=
  IsGenTransArea T I B (GC I B C)

end VAS5Reach



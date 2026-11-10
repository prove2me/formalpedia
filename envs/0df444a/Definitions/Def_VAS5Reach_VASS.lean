-- Prove2me | Definitions.Def_VAS5Reach_VASS
-- name    : VAS5Reach_VASS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:31.15621+00:00
-- url     : https://prove2.me/theorems/446abb8c-14f5-41e2-a4ee-a4da23646435
-- title:
--   Vector addition system with states (VASS) and its size
-- statement:
--   A $d$-dimensional **vector addition system with states** ($d$-VASS) is a pair $V = (Q, T)$ of a finite set $Q$ of states and a finite set $T \subseteq Q \times \mathbb Z^d \times Q$ of transitions. The module also defines
--   1. $\|T\| := \max_{(p,a,q) \in T} \|a\|$ (`normTrans`, $0$ for $T = \emptyset$);
--   2. $\mathrm{SIZE}(V) := |Q| + d\,|T|\,(\|T\| + 1) + 2$ (`size`), $\mathrm{SIZE}(V, s) := \mathrm{SIZE}(V) + d(\|s\| + 1)$ (`size2`) and $\mathrm{SIZE}(V, s, t) := \mathrm{SIZE}(V) + d(\|s\| + \|t\| + 1)$ (`size3`), where the norm of a configuration $p(x)$ is $\|x\|$;
--   3. a $d$-VAS $T \subseteq \mathbb Z^d$ as the one-state VASS (`ofVAS`);
--   4. the reverse $V^{\mathrm{REV}}$, which replaces every transition $(p, a, q)$ by $(q, -a, p)$ (`rev`).
--
--   **Formalization Note** States are drawn from an ambient type and the state set is a finite subset of it, so that sub-VASS and encodings share one ambient type; every transition connects states of $Q$.
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3 'VASS and VAS' and 'Size and Reachability Problems', pp.13–14 (PDF pp.15–16)

import Mathlib
import Definitions.Def_VAS5Reach_supNorm

namespace VAS5Reach

/-- A `d`-dimensional vector addition system with states (`d`-VASS) `V = (Q, T)`: a finite set of
states `Q` and a finite set of transitions `T ⊆ Q × ℤ^d × Q` whose source and target states lie
in `Q`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3 "VASS and VAS", printed
p. 13 (PDF p. 15): "A d-dimensional vector addition system with states (d-VASS) is a pair
V = (Q, T), where Q is a finite set of states and T ⊆ Q × Z^d × Q is a finite set of transitions."

**Formalization Note** States are drawn from an ambient type `S` and the state set is a `Finset S`,
so that sub-VASS (subsets of states and transitions) and `B`-encodings live in one ambient type.
Coordinates form an arbitrary finite type `ι` with `d = Fintype.card ι`. -/
structure VASS (S ι : Type) where
  /-- the finite state set `Q` -/
  states : Finset S
  /-- the finite transition set `T ⊆ Q × ℤ^d × Q` -/
  trans : Finset (S × (ι → ℤ) × S)
  /-- transitions connect states of `Q` -/
  trans_mem : ∀ τ ∈ trans, τ.1 ∈ states ∧ τ.2.2 ∈ states

namespace VASS

variable {S ι : Type}

/-- `∥T∥ := max_{(p,a,q)∈T} ∥a∥` (max norm; `0` for `T = ∅`). -/
def normTrans [Fintype ι] (V : VASS S ι) : ℕ :=
  V.trans.sup fun τ => supNorm τ.2.1

/-- `SIZE(V) := |Q| + d·|T|·(∥T∥ + 1) + 2` (printed p. 14, PDF p. 16). -/
def size [Fintype ι] (V : VASS S ι) : ℕ :=
  V.states.card + Fintype.card ι * V.trans.card * (V.normTrans + 1) + 2

/-- `SIZE(V, s) := SIZE(V) + d·(∥s∥ + 1)`, the size of a pair `(V, s)` with a configuration `s`
whose counter vector is `x` ("its size SIZE(V, s) is defined similarly", printed p. 14). -/
def size2 [Fintype ι] (V : VASS S ι) (x : ι → ℕ) : ℕ :=
  V.size + Fintype.card ι * (supNormN x + 1)

/-- `SIZE(V, s, t) := SIZE(V) + d·(∥s∥ + ∥t∥ + 1)` for configurations with counter vectors `x`,
`y` (printed p. 14, PDF p. 16). -/
def size3 [Fintype ι] (V : VASS S ι) (x y : ι → ℕ) : ℕ :=
  V.size + Fintype.card ι * (supNormN x + supNormN y + 1)

open Classical in
/-- A `d`-VAS with transition set `T ⊆ ℤ^d`, viewed as the one-state `d`-VASS with state `()`
("A d-dimensional vector addition system (d-VAS) is a d-VASS with a single state", p. 14). -/
noncomputable def ofVAS (T : Finset (ι → ℤ)) : VASS Unit ι where
  states := {()}
  trans := T.image fun a => ((), a, ())
  trans_mem := by intro τ _; simp

open Classical in
/-- The reverse `V^REV`, which replaces every transition `(p, a, q)` by `(q, −a, p)` (p. 14). -/
noncomputable def rev (V : VASS S ι) : VASS S ι where
  states := V.states
  trans := V.trans.image fun τ => (τ.2.2, -τ.2.1, τ.1)
  trans_mem := by
    intro τ h
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp h
    exact ⟨(V.trans_mem σ hσ).2, (V.trans_mem σ hσ).1⟩

end VASS

end VAS5Reach



-- Prove2me | Definitions.Def_VAS5Reach_Supplement_Factor
-- name    : VAS5Reach_Supplement_Factor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:49:16.413608+00:00
-- url     : https://prove2.me/theorems/de8b87ca-6e14-48bf-b255-09beac9a56b7
-- title:
--   Factors $[\![V]\!]_{I,B}$ and mixed LPS, their witnesses, and composition of relations
-- statement:
--   Let $V$ be a $d$-VAS with transition set $T$. A **factor** is either a $B$-encoding $[\![V]\!]_{I,B}$ ($I\subseteq[d]$, $B\in\mathbb N$) or a mixed LPS $\Lambda$. Its reachability relation is viewed on configurations of $V$:
--
--   1. for $[\![V]\!]_{I,B}$, a witness of length $n$ from $x$ to $y$ is a run of length $n$ of the published encoding from $\big((),x{\restriction}I\big)\big(x{\restriction}[d]\setminus I\big)$ to $\big((),y{\restriction}I\big)\big(y{\restriction}[d]\setminus I\big)$, where $x{\restriction}I,\ y{\restriction}I\in[0,B]^I$;
--   2. for a mixed LPS $\Lambda$, it is a witness of $x\xrightarrow{\Lambda}y$ of length $n$.
--
--   $\mathrm{Reach}_{V_i}$ is the set of pairs $(x,y)$ that have a witness. A factor is **bounded by $b$** if it is $[\![V]\!]_{I,B}$ with $|I|=3$ and $B\le b$, or a mixed LPS with $\|\Lambda\|\le b$ and $|\Lambda|\le b$. Relations are composed from left to right: $(s,t)\in R_1\circ R_2$ iff $(s,u)\in R_1$ and $(u,t)\in R_2$ for some $u$; the empty composition is the identity.
--
--   These are the factors of the polynomial factorization of Theorem C.1.
--
--   **Formalization Note** The encoding is the published `VAS5Reach.encode` of the one-state VASS `VASS.ofVAS T`, and runs are the published `VASS.IsRun`.
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem C.1, p.47 (PDF p.49); B-encoding pp.15–16 (PDF pp.17–18), relations viewed on configurations of V p.20 (PDF p.22); composition p.14 (PDF p.16)

import Mathlib
import Definitions.Def_VAS5Reach_VASS_IsRun
import Definitions.Def_VAS5Reach_encode
import Definitions.Def_VAS5Reach_Supplement_MixedLPS

namespace VAS5Reach.Supplement

open VAS5Reach

/-- A factor of a polynomial factorization of the reachability relation of a VAS `V`: either a
`B`-encoding `[[V]]_{I,B}` (`enc I B`) or a mixed LPS `Λ` (`lps Λ`).

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem C.1, printed p. 47
(PDF p. 49): "Vi has one of the following forms: 1. Vi = [[V]]I,B […] 2. Vi = Λ for some mixed LPS
Λ"; Theorem 1.3, printed p. 2 (PDF p. 4). -/
inductive Factor (ι : Type)
  | enc (I : Finset ι) (B : ℕ)
  | lps (Λ : MixedLPS ι)

namespace Factor

variable {ι : Type}

/-- `HasWitness T f x y n`: the factor `f`, built from the VAS with transition set `T`, has a
witness of length `n` from `x` to `y` (configurations of `V`, in `ℕ^d`).

* For `[[V]]_{I,B}`: `x↾I, y↾I ∈ [0, B]^I` and a run of length `n` from `((), x↾I)(x↾[d]∖I)` to
  `((), y↾I)(y↾[d]∖I)` in the published encoding `encode (VASS.ofVAS T) I B` (configurations of the
  encoding are viewed on configurations of `V` by restoring the counter values stored in the
  states, printed p. 20, PDF p. 22).
* For a mixed LPS `Λ`: a witness of `x −Λ→ y` of length `n`. -/
def HasWitness (T : Finset (ι → ℤ)) : Factor ι → (ι → ℕ) → (ι → ℕ) → ℕ → Prop
  | enc I B, x, y, n =>
      restrictI I x ∈ box I B ∧ restrictI I y ∈ box I B ∧
        ∃ π, (encode (VASS.ofVAS T) I B).IsRun ((), restrictI I x) (restrictC I x) π
          ((), restrictI I y) (restrictC I y) ∧ π.length = n
  | lps Λ, x, y, n => ∃ ws, Λ.IsWitness x ws y ∧ MixedLPS.witnessLength ws = n

/-- `Reach_{Vᵢ}` as a relation on `ℕ^d × ℕ^d`: some witness leads from `x` to `y`. -/
def Rel (T : Finset (ι → ℤ)) (f : Factor ι) (x y : ι → ℕ) : Prop :=
  ∃ n, HasWitness T f x y n

/-- The parameter bound of Theorem C.1 with bound `b`: an encoding has `|I| = 3` and `B ≤ b`; a
mixed LPS has `∥Λ∥ ≤ b` and `|Λ| ≤ b`. -/
def Bounded [Fintype ι] (b : ℕ) : Factor ι → Prop
  | enc I B => I.card = 3 ∧ B ≤ b
  | lps Λ => Λ.norm ≤ b ∧ Λ.size ≤ b

end Factor

/-- Left-to-right composition `R₁ ◦ ⋯ ◦ R_m` of a list of relations: `(s, t) ∈ R₁ ◦ R₂` iff
`(s, u) ∈ R₁` and `(u, t) ∈ R₂` for some `u` (printed p. 14, PDF p. 16); the empty composition is
the identity. -/
def relComp {α : Type} : List (α → α → Prop) → α → α → Prop
  | [], x, y => x = y
  | R :: Rs, x, y => ∃ u, R x u ∧ relComp Rs u y

end VAS5Reach.Supplement



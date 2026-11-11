-- Prove2me | Definitions.Def_CapacitatedKMedianFPT_Main_Encoding
-- name    : CapacitatedKMedianFPT_Main_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:14:27.849384+00:00
-- url     : https://prove2.me/theorems/ab1a4890-0fad-41a7-ac09-6340c3616cd4
-- title:
--   Input and output encodings of capacitated k-median, perfect families and oracle submodular maximization
-- statement:
--   How the algorithms of the mission receive their inputs and return their outputs.
--
--   1. A **rational instance** has points $0,\dots,m-1$, a rational distance table, client and facility flags (a point may carry both), capacities and $k$. It describes the instance with real distances $d(x,y)$ given by the table. Its encoding is the list $m,k$, the client flags, the facility flags, the capacities, and the distance table row by row.
--   2. An output of a capacitated $k$-median algorithm is read from the final memory: cells $0,\dots,k-1$ contain facilities $s_0,\dots,s_{k-1}$ and cell $k+c$ contains $\varphi(c)$ for every client $c$. It is **correct with ratio $\rho$** if the $s_j$ are distinct and $(\{s_j\},\varphi)$ is a solution of cost at most $\rho\cdot\mathrm{OPT}$.
--   3. For Theorem 3 the input is $(m,N)$ with points $\{0,\dots,N-1\}$; cell $0$ holds the family size $\tau$ and cell $1+hN+x$ holds the color $h(x)\in\{0,\dots,m-1\}$. The output is correct if $\tau$ is within the bound and the family is **$m$-perfect**: every $m$-element set $O$ satisfies $|h(O)|=m$ for some member $h$.
--   4. For Theorem 4 the input is $n,k,\varepsilon$, the part index of each element of $\{0,\dots,n-1\}$ and its capacity; the value oracle of $v:2^{[n]}\to\mathbb Q$ answers a query with $v$ of the set of element labels among the queried cells. Cell $0$ of the output holds $\tau$ and cell $1+jk+i$ holds the element $s^i_j$ of $S_j\cap F_i$.
--
--   **Formalization Note** Colors $[m]=\{1,\dots,m\}$ are relabelled $0,\dots,m-1$. Clients and facilities are identified with their indices.
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 1–2, Theorem 1; p. 5, §2 Instances; p. 6, Color coding and Theorem 3; p. 13, Theorem 4

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_Instance
import Definitions.Def_CapacitatedKMedianFPT_Main_Machine

set_option autoImplicit false

/-!
# Input and output encodings for the algorithmic statements

Theorem 1 and Lemma 1 (capacitated k-median algorithms), Theorem 3 (perfect families) and
Theorem 4 (capacity-preserving submodular maximization) of Anand–Huang–Jaiswal–Kumar–Lee–Yadav,
STOC 2027 submission #1646.
-/

namespace CapacitatedKMedianFPT.Main

open scoped BigOperators

noncomputable section

/-- An instance as an algorithm receives it: points `0, …, m-1`, a rational distance table, client
and facility flags (a point may be both), capacities and `k`. -/
structure RatInstance where
  m : ℕ
  d : Fin m → Fin m → ℚ
  isClient : Fin m → Bool
  isFacility : Fin m → Bool
  U : Fin m → ℕ
  k : ℕ

namespace RatInstance

/-- The mathematical instance described by the table (distances read as reals). -/
def toInstance (I : RatInstance) : Instance (Fin I.m) where
  d := fun x y => (I.d x y : ℝ)
  C := Finset.univ.filter (fun x => I.isClient x = true)
  F := Finset.univ.filter (fun x => I.isFacility x = true)
  U := I.U
  k := I.k

/-- The standard encoding: `m, k`, the client flags, the facility flags, the capacities, then the
distance table row by row. -/
def encode (I : RatInstance) : List ℚ :=
  [(I.m : ℚ), (I.k : ℚ)] ++
    List.ofFn (fun x => if I.isClient x then (1 : ℚ) else 0) ++
    List.ofFn (fun x => if I.isFacility x then (1 : ℚ) else 0) ++
    List.ofFn (fun x => (I.U x : ℚ)) ++
    (List.ofFn (fun x => List.ofFn (fun y => I.d x y))).flatten

/-- Output convention for a capacitated k-median algorithm: after halting, cells `0, …, k-1` hold
the `k` open facilities `s_0, …, s_{k-1}` and cell `k + c` holds `φ(c)` for every client `c`. The
output is correct with ratio `ρ` if the facilities are distinct and `(S, φ)` is a solution of cost
at most `ρ · OPT`. -/
def IsSolutionOutput (I : RatInstance) (ρ : ℝ) (mem : Memory) : Prop :=
  ∃ (s : Fin I.k → Fin I.m) (φ : Fin I.m → Fin I.m),
    (∀ j : Fin I.k, mem (j : ℕ) = ((s j : ℕ) : ℚ)) ∧
    (∀ c : Fin I.m, I.isClient c = true → mem ((I.k : ℤ) + (c : ℕ)) = ((φ c : ℕ) : ℚ)) ∧
    Function.Injective s ∧ I.toInstance.IsApprox ρ (Finset.univ.image s) φ

end RatInstance

/-- Output convention for Theorem 3: cell `0` holds the family size `τ`, and cell
`1 + h·N + x` holds `h(x) ∈ {0, …, m-1}` for `h < τ`, `x < N`. Correct if the family has at most
`bound` members and is `m`-perfect: every `m`-element subset of the `N` points is colored
injectively by some member. -/
def IsPerfectFamilyOutput (m N : ℕ) (bound : ℝ) (mem : Memory) : Prop :=
  ∃ (τ : ℕ) (col : Fin τ → Fin N → Fin m),
    mem 0 = (τ : ℚ) ∧
    (∀ (h : Fin τ) (x : Fin N), mem (1 + (h : ℕ) * N + (x : ℕ) : ℕ) = ((col h x : ℕ) : ℚ)) ∧
    (τ : ℝ) ≤ bound ∧
    ∀ O : Finset (Fin N), O.card = m → ∃ h : Fin τ, (O.image (col h)).card = m

/-- Input of Theorem 4: `n, k, ε`, the part index of each element, its capacity. -/
def submodInput (n k : ℕ) (ε : ℚ) (part : Fin n → Fin k) (U : Fin n → ℕ) : List ℚ :=
  [(n : ℚ), (k : ℚ), ε] ++ List.ofFn (fun x => ((part x : ℕ) : ℚ)) ++
    List.ofFn (fun x => (U x : ℚ))

/-- The value oracle of `v : 2^{[n]} → ℚ`: a query returns `v` of the set of elements whose labels
occur among the queried cells. -/
def setOracle (n : ℕ) (v : Finset (Fin n) → ℚ) : Oracle :=
  fun xs => v (Finset.univ.filter (fun x : Fin n => ((x : ℕ) : ℚ) ∈ xs))

/-- Output convention for Theorem 4: cell `0` holds `τ`, and cell `1 + j·k + i` holds the label of
the element `s_j^i` of `S_j ∩ F_i`. -/
def IsTransversalFamilyOutput (n k : ℕ) (mem : Memory) (τ : ℕ) (sel : Fin τ → Fin k → Fin n) :
    Prop :=
  mem 0 = (τ : ℚ) ∧
    ∀ (j : Fin τ) (i : Fin k), mem (1 + (j : ℕ) * k + (i : ℕ) : ℕ) = ((sel j i : ℕ) : ℚ)

end

end CapacitatedKMedianFPT.Main



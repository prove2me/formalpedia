-- Prove2me | Definitions.Def_NetworkSumSecure_Solvability_encoding
-- name    : NetworkSumSecure_Solvability_encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T05:02:53.352874+00:00
-- url     : https://prove2.me/theorems/e301bdfd-8d10-4dae-8924-d1c9fe9207d3
-- title:
--   Causal scalar linear schemes and exact sum-security
-- statement:
--   Fix a network $N$, a finite field $F$, and nonnegative key counts $z_i$. User $i$ holds an arbitrary deterministic input $m_i\in F$ and a private uniformly sampled vector $k_i\in F^{z_i}$. The key space $K=\prod_{i\in U}F^{z_i}$ carries the uniform product law. Its user factors are independent, including singleton factors when $z_i=0$.
--
--   Local coefficient data specifies each user's linear encoder using only its own $(m_i,k_i)$ and each relay's linear encoder using only incoming edge symbols. A topological fold executes these operations from a zero initial edge state. The server's decoder is a linear functional of its incoming symbols. Correctness requires its output to equal $\sum_i m_i$ for every input and key tuple.
--
--   For an edge set $W$, observation $y\in F^W$ and sum value $a\in F$, define
--
--   $$\mathcal K_W(a,y)=\{k\in K:\exists m\in F^U,\ \sum_i m_i=a\text{ and }\operatorname{execute}(m,k)|_W=y\}.$$
--
--   The probability is exactly $|\mathcal K_W(a,y)|/|K|$ in $\mathbb Q$. Sum-security requires equality of these probabilities for every $a,b\in F$, every $|W|\le r$, and every observation. Each key is counted once, inputs are not sampled, and the existential input witnesses are not counted. A scheme is feasible when it is correct and sum-secure; solvability existentially chooses the key counts, local coefficients, topological order and decoder.
--
--   Global columns are derived afterwards by executing the local code on every standard-basis input in user-block coordinates $(m_i,k_i)$. This layer supplies the operational meaning used by the goal.
-- source:
--   Yang Bai, Xuan Guang, Lizhi Wang, STOC 2027 submission #1291 (October 2026), pp. 6–8 (PDF pp. 8–10), Definition 1 and equations (1)–(7)

import Mathlib
import Definitions.Def_NetworkSumSecure_Solvability_network

open scoped BigOperators

namespace NetworkSumSecure.Solvability

/-! Definition 1 and equations (1)–(7), printed pp.6–8 (PDF 8–10).
Local executions are defined before any global vector or algebraic criterion. -/

variable {V E U F : Type}

/-- User-block coordinates: none is the message, some j is key coordinate j. -/
abbrev Coord (z : U → ℕ) := (i : U) × Option (Fin (z i))
abbrev Keys (F : Type) (z : U → ℕ) := (i : U) → Fin (z i) → F

/-- Raw local coefficients. Only the selected user's coefficients, or the incoming
edges' coefficients at a relay, are used. No success certificates are stored. -/
structure LocalCode [Fintype E] (N : Network V E U) (F : Type) (z : U → ℕ) where
  order : EdgeOrder N
  userCoeff : (i : U) → E → Option (Fin (z i)) → F
  relayCoeff : E → E → F

noncomputable def localSymbol [Field F] [Fintype E]
    {N : Network V E U} {z : U → ℕ} (C : LocalCode N F z)
    (m : U → F) (k : Keys F z) (state : E → F) (e : E) : F := by
  classical
  exact if h : ∃ i, N.graph.tail e = N.user i then
    let i := Classical.choose h
    m i * C.userCoeff i e none + ∑ j, k i j * C.userCoeff i e (some j)
  else ∑ d ∈ incoming N (N.graph.tail e), C.relayCoeff d e * state d

/-- Finite causal execution, starting with zero on every edge and updating each once. -/
noncomputable def execute [Field F] [Fintype E]
    {N : Network V E U} {z : U → ℕ} (C : LocalCode N F z)
    (m : U → F) (k : Keys F z) : E → F := by
  classical
  exact (List.ofFn C.order.edge).foldl
    (fun state e => Function.update state e (localSymbol C m k state e)) (fun _ => 0)

abbrev Decoder (N : Network V E U) (F : Type) :=
  {e : E // N.graph.head e = N.server} → F

noncomputable def decoded [Field F] [Fintype E]
    {N : Network V E U} {z : U → ℕ} (C : LocalCode N F z)
    (φ : Decoder N F) (m : U → F) (k : Keys F z) : F := by
  classical
  exact ∑ e : {e : E // N.graph.head e = N.server}, φ e * execute C m k e.val

def Correct [Field F] [Fintype E] [Fintype U]
    {N : Network V E U} {z : U → ℕ} (C : LocalCode N F z) (φ : Decoder N F) : Prop :=
  ∀ m k, decoded C φ m k = ∑ i, m i

/-- A set of keys, with an existential deterministic input witness. -/
noncomputable def keyEvent [Field F] [Fintype E] [Fintype U] [Fintype F]
    {N : Network V E U} {z : U → ℕ} (C : LocalCode N F z)
    (W : Finset E) (a : F) (y : (e : W) → F) : Finset (Keys F z) := by
  classical
  exact Finset.univ.filter (fun k => ∃ m : U → F,
    (∑ i, m i) = a ∧ ∀ e : W, execute C m k e.val = y e)

/-- Exact rational probability under the independent uniform private-key product. -/
noncomputable def keyProbability [Field F] [Fintype E] [Fintype U] [Fintype F]
    {N : Network V E U} {z : U → ℕ} (C : LocalCode N F z)
    (W : Finset E) (a : F) (y : (e : W) → F) : ℚ := by
  classical
  exact ((keyEvent C W a y).card : ℚ) / (Fintype.card (Keys F z) : ℚ)

def SumSecure [Field F] [Fintype E] [Fintype U] [Fintype F]
    {N : Network V E U} {z : U → ℕ} (C : LocalCode N F z) (r : ℕ) : Prop :=
  ∀ W : Finset E, W.card ≤ r → ∀ (y : (e : W) → F) (a b : F),
    keyProbability C W a y = keyProbability C W b y

def Feasible [Field F] [Fintype E] [Fintype U] [Fintype F]
    {N : Network V E U} {z : U → ℕ} (C : LocalCode N F z)
    (φ : Decoder N F) (r : ℕ) : Prop := Correct C φ ∧ SumSecure C r

def Solvable [Field F] [Fintype E] [Fintype U] [Fintype F]
    (N : Network V E U) (r : ℕ) : Prop :=
  ∃ (z : U → ℕ) (C : LocalCode N F z) (φ : Decoder N F), Feasible C φ r

/-- The global column is induced by actual executions at standard-basis inputs. -/
noncomputable def globalColumn [Field F] [Fintype E]
    {N : Network V E U} {z : U → ℕ} (C : LocalCode N F z) (e : E) : Coord z → F := by
  classical
  exact fun c => execute C
    (fun i => if c = ⟨i, none⟩ then 1 else 0)
    (fun i j => if c = ⟨i, some j⟩ then 1 else 0) e

end NetworkSumSecure.Solvability



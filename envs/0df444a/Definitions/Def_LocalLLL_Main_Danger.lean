-- Prove2me | Definitions.Def_LocalLLL_Main_Danger
-- name    : LocalLLL_Main_Danger
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:19.136495+00:00
-- url     : https://prove2.me/theorems/7a727cfe-ba6c-4ec8-b072-62228dda469a
-- title:
--   Retraction marginals, dangerous events and the amplified LLL
-- statement:
--   For an event set $U$, retraction erases $W=\bigcup_{u\in U}V_u$. Given full assignments $x,z$, the splice takes $z$ on $W$ and $x$ elsewhere. The retracted marginal is the product-law probability that this splice belongs to the event.
--
--   Put $k=\lfloor\lambda/16\rfloor$, $q=d^{-\lambda/32}$ and $\rho=d^{-19\lambda/32}$. The dangerous event $D_v$ consists of assignments $x$ with
--
--   $$\exists T\subseteq B_G(v,5),\quad |T|\le k,\quad \Pr_{\mathrm{ret}(x,B_G(T,4))}[A_v]>q.$$
--
--   The amplified event $F_v$ is the existence in $B_G(v,11)$ of a 2-independent set of $k+1$ dangerous vertices. Its coordinate set is $\bigcup_{u\in B_G(v,11)}V_u$. Bounded danger means avoidance of all $F_v$. A transformation label supplies the original local event and coordinate set, this amplified coordinate set, and the values of $x$ only on that set. These constructions retain the original variable universe and laws. The natural floor is used only with $\lambda\ge1000$ in the statements.
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), §3.2 dangerous-event definition and Claim 3.2, p. 4 (PDF 5); Part II, p. 5 (PDF 6); Lemma 3.1, p. 3 (PDF 4); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib
import Definitions.Def_LocalLLL_Main_VariableInstance

noncomputable section

namespace LocalLLL.Main

open MeasureTheory

variable {ι V : Type} {α : ι → Type} [∀ z, MeasurableSpace (α z)]

def variablesOf (vars : V → Set ι) (U : Set V) : Set ι := {z | ∃ u ∈ U, z ∈ vars u}

/-- Resample W from z and retain x outside W. No conditioning on a null event is used. -/
def splice (x z : Assignment α) (W : Set ι) : Assignment α := by
  classical
  exact fun i => if i ∈ W then z i else x i

def marginal (μ : ∀ z, Measure (α z)) (x : Assignment α) (W : Set ι)
    (E : Set (Assignment α)) : ℝ := probability μ {z | splice x z W ∈ E}

def retractedMarginal (μ : ∀ z, Measure (α z)) (vars : V → Set ι)
    (x : Assignment α) (U : Set V) (E : Set (Assignment α)) : ℝ :=
  marginal μ x (variablesOf vars U) E

def packingSize (lam : ℝ) : ℕ := ⌊lam / 16⌋₊
def dangerThreshold (d : ℕ) (lam : ℝ) : ℝ := (d : ℝ) ^ (-lam / 32)
def dangerBound (d : ℕ) (lam : ℝ) : ℝ := (d : ℝ) ^ (-19 * lam / 32)

def dangerous (μ : ∀ z, Measure (α z)) (G : SimpleGraph V) (vars : V → Set ι)
    (events : V → Set (Assignment α)) (d : ℕ) (lam : ℝ) (v : V) : Set (Assignment α) :=
  {x | ∃ T : Finset V, (↑T : Set V) ⊆ ball G v 5 ∧ T.card ≤ packingSize lam ∧
    dangerThreshold d lam < retractedMarginal μ vars x (balls G (↑T) 4) (events v)}

/-- The amplified event F_v, on the same variable universe and laws. -/
def amplifiedEvent (μ : ∀ z, Measure (α z)) (G : SimpleGraph V) (vars : V → Set ι)
    (events : V → Set (Assignment α)) (d : ℕ) (lam : ℝ) (v : V) : Set (Assignment α) :=
  {x | ∃ S : Finset V, (↑S : Set V) ⊆ ball G v 11 ∧
    S.card = packingSize lam + 1 ∧ separated G 2 (↑S) ∧
    ∀ u ∈ S, x ∈ dangerous μ G vars events d lam u}

def amplifiedVars (G : SimpleGraph V) (vars : V → Set ι) (v : V) : Set ι :=
  variablesOf vars (ball G v 11)

def boundedDanger (μ : ∀ z, Measure (α z)) (G : SimpleGraph V) (vars : V → Set ι)
    (events : V → Set (Assignment α)) (d : ℕ) (lam : ℝ) (x : Assignment α) : Prop :=
  ∀ v, x ∉ amplifiedEvent μ G vars events d lam v

/-- A transformation input contains values only on a locally supplied variable set U. -/
abbrev TransformInput (ι : Type) (α : ι → Type) :=
  LLLInput ι α × ((U : Set ι) × ((z : U) → α z.1))

def transformLabels (G : SimpleGraph V)
    (vars : V → Set ι) (events : V → Set (Assignment α)) (x : Assignment α) :
    V → TransformInput ι α :=
  fun v => ((vars v, events v), ⟨amplifiedVars G vars v, fun z => x z.1⟩)
end LocalLLL.Main



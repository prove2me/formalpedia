-- Prove2me | Definitions.Def_ElimAgree_Supplement_Models
-- name    : ElimAgree_Supplement_Models
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:33:28.288252+00:00
-- url     : https://prove2.me/theorems/10dfcaf9-a132-4a62-a146-d82c98db5964
-- title:
--   Elimination of general functions, Alice-output and one-way protocols, expected communication
-- statement:
--   For Boolean functions $f_i:\mathcal X_i\times\mathcal Y_i\to\{0,1\}$, $i\in[k]$, the problem $\mathrm{Elim}(f_1,\dots,f_k)$ gives Alice $X=(x_1,\dots,x_k)$ and Bob $Y=(y_1,\dots,y_k)$; the answer vector is
--
--   $$F(X,Y)=\big(f_1(x_1,y_1),\dots,f_k(x_k,y_k)\big)\in\{0,1\}^k,$$
--
--   and an output $\sigma$ is correct when $\sigma\neq F(X,Y)$. $\mathrm{Elim}(f^k)$ is the case $f_1=\dots=f_k=f$.
--
--   Protocols are probability distributions over the published deterministic protocol trees (public coins, private coins allowed), as in the base mission. Three leaf conventions are used: in an **Alice-output** protocol each leaf carries Alice's output as a function of her input, and a run fails when this output equals $F(X,Y)$; the **common-output** and **designated-party** conventions are the base mission's. A tree is **one-way from Bob to Alice** if only Bob speaks (his message is the root-to-leaf path), and **Bob-then-Alice** if on every path all of Bob's nodes precede all of Alice's.
--
--   The communication of a run is the length of the root-to-leaf path it follows. The **worst-case expected communication** of a protocol $\mu$ is
--
--   $$\max_{(X,Y)}\ \mathbb E_{T\sim\mu}\big[\text{length of the path of }T\text{ on }(X,Y)\big].$$
--
--   These are the models of Definition 2.1 and Appendix C used by the supplement's theorems.
--
--   **Formalization Note** The input types of the $f_i$ may depend on $i$. Expectations are in $[0,\infty]$ (`ENNReal`).
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Definition 2.1, p.6 (PDF p.8); Elim, p.1 (PDF p.3); §3.8, p.15 (PDF p.17); Theorem B.6, p.34 (PDF p.36); Appendix C, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_ElimAgree_ComLabel

namespace ElimAgree

namespace Supplement

/-!
# Elimination of general functions, output conventions, one-way trees, expected communication

Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*,
manuscript (STOC 2027 submission), §1 (p.1), Definition 2.1 (p.6), §3.8 (p.15), Appendix C (p.36).

**Formalization Note.**
* A public-coin protocol (private coins allowed) is a `PMF` over the published deterministic trees
  `OneOfManyCC.Protocol α β L`, as in the base mission (`ElimAgree.CostLE`). The leaf label `L`
  fixes the output convention: `α → O` is local output by Alice (her output is a function of her
  input; coins and transcript are fixed by the leaf), `ComLabel α β O` is common output and
  `(α → O) ⊕ (β → O)` is the output party designated at each leaf (base `desErr`).
* "Bob sends one message and Alice outputs" is a tree all of whose internal nodes are Bob's
  (`IsOneWayBA`): Bob's message is the root-to-leaf path. "One message from Bob followed by one
  message from Alice" is `IsBobThenAlice`.
* The communication of a run is the length of the root-to-leaf path it follows (`pathLen`);
  transcripts of a protocol tree are prefix-free. The worst-case expected communication of `μ` is
  the supremum over inputs of the expectation over `μ` of `pathLen` (`worstExpComm`), in `ℝ≥0∞`.
-/

/-- The answer vector of `Elim(f_1, …, f_k)` (§1, p.1): `F(X, Y)_i = f_i(x_i, y_i)`. The input
types may depend on `i`; `Elim(f^k)` is the constant family `fun _ => f`. -/
def elimAns {k : ℕ} {X Y : Fin k → Type} (f : ∀ i, X i → Y i → Bool) :
    (∀ i, X i) → (∀ i, Y i) → Fin k → Bool :=
  fun x y i => f i (x i) (y i)

/-- Trees of an Alice-output protocol: each leaf carries Alice's output as a function of her
input (Definition 2.1, `R^{pub,A}`). -/
abbrev AliceProt (α β O : Type) : Type := OneOfManyCC.Protocol α β (α → O)

/-- Trees of a common-output protocol (Definition 2.1, `R^{pub,com}`; base `ComLabel`). -/
abbrev ComProtG (α β O : Type) : Type := OneOfManyCC.Protocol α β (ComLabel α β O)

/-- Trees of a protocol whose output party is designated at each leaf (base `desErr`). -/
abbrev DesProt (α β O : Type) : Type := OneOfManyCC.Protocol α β ((α → O) ⊕ (β → O))

/-- Failure probability on input `(x, y)` of an Alice-output protocol for `Elim(F)`: the run fails
iff Alice's output equals the answer vector `F(x, y)` (Definition 2.1, p.6). -/
noncomputable def aliceErr {α β O : Type} (F : α → β → O) (μ : PMF (AliceProt α β O)) (x : α)
    (y : β) : ENNReal :=
  failProb μ x y (fun o => o x = F x y)

/-- A tree in which only Bob speaks: one message from Bob (the path), then the leaf (§3.8, p.15;
Definition 2.1, `D^{B→A,A}`). -/
def IsOneWayBA {α β L : Type} : OneOfManyCC.Protocol α β L → Prop
  | .leaf _ => True
  | .alice _ _ _ => False
  | .bob _ p₀ p₁ => IsOneWayBA p₀ ∧ IsOneWayBA p₁

/-- A tree in which only Alice speaks. -/
def IsAliceOnly {α β L : Type} : OneOfManyCC.Protocol α β L → Prop
  | .leaf _ => True
  | .alice _ p₀ p₁ => IsAliceOnly p₀ ∧ IsAliceOnly p₁
  | .bob _ _ _ => False

/-- One message from Bob followed by one message from Alice (Theorem B.6, p.34): along every
path all of Bob's nodes come before all of Alice's. -/
def IsBobThenAlice {α β L : Type} : OneOfManyCC.Protocol α β L → Prop
  | .leaf _ => True
  | .alice _ p₀ p₁ => IsAliceOnly p₀ ∧ IsAliceOnly p₁
  | .bob _ p₀ p₁ => IsBobThenAlice p₀ ∧ IsBobThenAlice p₁

/-- The number of bits sent on input `(x, y)`: the length of the root-to-leaf path followed. -/
def pathLen {α β L : Type} : OneOfManyCC.Protocol α β L → α → β → ℕ
  | .leaf _, _, _ => 0
  | .alice s p₀ p₁, x, y => (if s x = true then pathLen p₁ x y else pathLen p₀ x y) + 1
  | .bob s p₀ p₁, x, y => (if s y = true then pathLen p₁ x y else pathLen p₀ x y) + 1

/-- Expected communication of the public-coin protocol `μ` on input `(x, y)`. -/
noncomputable def expComm {α β L : Type} (μ : PMF (OneOfManyCC.Protocol α β L)) (x : α) (y : β) :
    ENNReal :=
  ∑' T, μ T * (pathLen T x y : ENNReal)

/-- Worst-case expected communication (Appendix C, p.36; proof of Corollary A.3, p.30): the
maximum over inputs of the expected length of the transcript. -/
noncomputable def worstExpComm {α β L : Type} (μ : PMF (OneOfManyCC.Protocol α β L)) : ENNReal :=
  ⨆ x, ⨆ y, expComm μ x y

end Supplement

end ElimAgree



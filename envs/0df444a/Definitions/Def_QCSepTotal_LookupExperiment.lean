-- Prove2me | Definitions.Def_QCSepTotal_LookupExperiment
-- name    : QCSepTotal_LookupExperiment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:38:26.443248+00:00
-- url     : https://prove2.me/theorems/14374273-17a7-4ae0-9540-30d741ee4f14
-- title:
--   The random experiment of Section 4.1: $T$, $L$, $\Pi_i$, assumptions (7) and (8), $Q_{x,y}$, $Q^{\hat u,\hat v}_{x,y}$
-- statement:
--   Fix a partial function $F$, a distribution $\mu$ supported on $\mathrm{dom}(F)$, parameters $c,b$, fixed-seed maps $E_\ell$, and a randomized protocol $\Pi$ on the inputs $(x,U)$, $(y,V)$ of $F_{\mathrm{tot}}$. The **joint input** is $T=(X_1,\dots,X_c,U,Y_1,\dots,Y_c,V)$, where the pairs $(X_i,Y_i)$ are independent samples from $\mu$ and $U,V$ are independent uniform elements of $\mathbb F_2^{4b}$, independent of these pairs; the coins of $\Pi$ are drawn independently of everything else. Write $X=(X_1,\dots,X_c)$, $Y=(Y_1,\dots,Y_c)$, $L_i=F(X_i,Y_i)$, $L=(L_1,\dots,L_c)$. Let $\Pi$ also denote the **transcript** of the protocol, consisting of its public coins and communicated messages, and let $\Pi_i=(\Pi,X_{-i},U,Y_{-i},V)$. Set $\delta=1/(10^{22}c)$.
--
--   1. **Assumption (7):** with $W$ uniform on $\{0,1\}^c$, $\Delta(X^L, X\otimes W)\le c\delta/3$ and $\Delta(Y^L, Y\otimes W)\le c\delta/3$.
--   2. **Assumption (8):** $I(L_i:\Pi_i\mid X_i)\le\delta$ and $I(L_i:\Pi_i\mid Y_i)\le\delta$ for every $i\in[c]$.
--   3. For $(x,y)$ in the support of $XY$, $Q_{x,y}$ is the distribution of $\Pi$ conditioned on $X=x$, $Y=y$. For $\hat u,\hat v\in\mathbb F_2^b$, $Q^{\hat u,\hat v}_{x,y}$ is its distribution conditioned in addition on $E_\ell(U)=\hat u$ and $E_\ell(V)=\hat v$, where $\ell=L(x,y)$.
--
--   These objects state Lemma 4.2.
--
--   **Formalization Note** $X^L$ is the joint law of $(X,L)$, as in the proof of Lemma 2.1; $W$ is uniform on $\mathbb F_2^c$. Conditional mutual information is the published `MultiphaseDisj.condMI` in bits, $I(A:B\mid C)=H(A\mid C)-H(A\mid B,C)$. The conditional laws are taken on the full sample space, so they are literally the conditionings of the paper; they are only read on events of positive probability.
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), §4.1, pp.7–9 (δ = 1/(10^22 c), p.7; T, L, Π_i, p.8; (7), p.8; (8), Q_{x,y}, Q^{û,v̂}_{x,y}, p.9)

import Mathlib
import Definitions.Def_MultiphaseDisj_FiniteInfo
import Definitions.Def_QCSepTotal_tv
import Definitions.Def_QCSepTotal_RandProtocol
import Definitions.Def_QCSepTotal_Ftot

namespace QCSepTotal

/-- The random experiment of Section 4.1 (F. Le Gall, *Improved Separations between Quantum and
Classical Communication Complexity of Total Functions*, arXiv:2609.16726, held version sha256
970e1476…, pp.7–9) for a protocol `P` on the inputs of `Ftot` (Alice holds `(x, U)`, Bob holds
`(y, V)`). The sample space consists of the `c` input pairs `(X_i, Y_i)`, the two cells
`U, V ∈ F₂^{4b}` and all randomness of `P` (public coins `R`, Alice's and Bob's private coins). -/
abbrev LookupSample (X Y : Type) (c b : ℕ)
    (P : RandProtocol ((Fin c → X) × (Fin (4 * b) → ZMod 2)) ((Fin c → Y) × (Fin (4 * b) → ZMod 2))) :
    Type :=
  (Fin c → X × Y) × (Fin (4 * b) → ZMod 2) × (Fin (4 * b) → ZMod 2) × (P.Pub × P.PrivA × P.PrivB)

namespace LookupSample

variable {X Y : Type} {c b : ℕ}
  {P : RandProtocol ((Fin c → X) × (Fin (4 * b) → ZMod 2)) ((Fin c → Y) × (Fin (4 * b) → ZMod 2))}

/-- `X = (X_1, …, X_c)`. -/
def xs (ω : LookupSample X Y c b P) : Fin c → X := fun i => (ω.1 i).1
/-- `Y = (Y_1, …, Y_c)`. -/
def ys (ω : LookupSample X Y c b P) : Fin c → Y := fun i => (ω.1 i).2
/-- Alice's cell `U`. -/
def U (ω : LookupSample X Y c b P) : Fin (4 * b) → ZMod 2 := ω.2.1
/-- Bob's cell `V`. -/
def V (ω : LookupSample X Y c b P) : Fin (4 * b) → ZMod 2 := ω.2.2.1
/-- `L = (L_1, …, L_c)`, `L_i = F(X_i, Y_i)` (p.8). -/
def Ls (F : PartialFn X Y) (ω : LookupSample X Y c b P) : Fin c → ZMod 2 :=
  addr F (xs ω) (ys ω)
/-- The transcript `Π` of the protocol: its public coins `R` and its communicated messages
(p.7: "The private randomness and the inputs `x, y, U, V` are not included in the transcript").
-/
def transcript (ω : LookupSample X Y c b P) : P.Pub × List Bool :=
  (ω.2.2.2.1, trace (P.tree ω.2.2.2.1) ((xs ω, U ω), ω.2.2.2.2.1) ((ys ω, V ω), ω.2.2.2.2.2))
/-- The transcript of the protocol `Π_i` of p.8, `Π_i = (Π, X_{−i}, U, Y_{−i}, V)`. -/
def transcriptI (i : Fin c) (ω : LookupSample X Y c b P) :
    (P.Pub × List Bool) × ({j : Fin c // j ≠ i} → X) × (Fin (4 * b) → ZMod 2) ×
      ({j : Fin c // j ≠ i} → Y) × (Fin (4 * b) → ZMod 2) :=
  (transcript ω, fun j => xs ω j.1, U ω, fun j => ys ω j.1, V ω)

end LookupSample

open LookupSample

variable {X Y : Type} [Fintype X] [Fintype Y] {c b : ℕ}

/-- The law of the sample (p.8): the pairs `(X_i, Y_i)` are independent samples from `µ`, the
cells `U, V` are independent uniform elements of `F₂^{4b}`, independent of these pairs, and the
coins of `P` are drawn from their laws, independently of everything else. -/
noncomputable def lookupLaw (μ : PMF (X × Y))
    (P : RandProtocol ((Fin c → X) × (Fin (4 * b) → ZMod 2)) ((Fin c → Y) × (Fin (4 * b) → ZMod 2))) :
    PMF (LookupSample X Y c b P) :=
  prodLaw (iidLaw μ c) (prodLaw (PMF.uniformOfFintype (Fin (4 * b) → ZMod 2))
    (prodLaw (PMF.uniformOfFintype (Fin (4 * b) → ZMod 2)) P.coins))

/-- The constant `δ = 1/(10²² c)` of the proof of Theorem 4.1 (p.7). -/
noncomputable def deltaC (c : ℕ) : ℝ := 1 / (10 ^ 22 * (c : ℝ))

/-- **Assumption (7)** (p.8): with `W` uniform on `{0, 1}^c`,
`Δ(X^L, X ⊗ W) ≤ cδ/3` and `Δ(Y^L, Y ⊗ W) ≤ cδ/3`.

**Formalization Note.** `X^L` is the joint law of `(X, L)` (as in the proof of Lemma 2.1, p.3);
`W` is uniform on `F₂^c`, the type of `L`. -/
def Assumption7 (F : PartialFn X Y) (μ : PMF (X × Y))
    (P : RandProtocol ((Fin c → X) × (Fin (4 * b) → ZMod 2)) ((Fin c → Y) × (Fin (4 * b) → ZMod 2)))
    (δ : ℝ) : Prop :=
  tv ((lookupLaw μ P).map fun ω => (xs ω, Ls F ω))
      (prodLaw ((lookupLaw μ P).map xs) (PMF.uniformOfFintype (Fin c → ZMod 2))) ≤ c * δ / 3 ∧
  tv ((lookupLaw μ P).map fun ω => (ys ω, Ls F ω))
      (prodLaw ((lookupLaw μ P).map ys) (PMF.uniformOfFintype (Fin c → ZMod 2))) ≤ c * δ / 3

/-- **Assumption (8)** (p.9): `I(L_i : Π_i | X_i) ≤ δ` and `I(L_i : Π_i | Y_i) ≤ δ` for every
`i ∈ [c]`, with conditional mutual information in bits (`MultiphaseDisj.condMI`, which is
`I(A : B | C) = H(A | C) − H(A | B, C)`, as on p.3). -/
def Assumption8 (F : PartialFn X Y) (μ : PMF (X × Y))
    (P : RandProtocol ((Fin c → X) × (Fin (4 * b) → ZMod 2)) ((Fin c → Y) × (Fin (4 * b) → ZMod 2)))
    (δ : ℝ) : Prop :=
  ∀ i : Fin c,
    MultiphaseDisj.condMI (fun ω => (lookupLaw μ P ω).toReal) (fun ω => Ls F ω i)
        (transcriptI i) (fun ω => xs ω i) ≤ δ ∧
    MultiphaseDisj.condMI (fun ω => (lookupLaw μ P ω).toReal) (fun ω => Ls F ω i)
        (transcriptI i) (fun ω => ys ω i) ≤ δ

/-- `Q_{x,y} = Π^{x,y}` (p.9): the law of the transcript `Π` conditioned on `X = x, Y = y`. -/
noncomputable def Qxy (μ : PMF (X × Y))
    (P : RandProtocol ((Fin c → X) × (Fin (4 * b) → ZMod 2)) ((Fin c → Y) × (Fin (4 * b) → ZMod 2)))
    (x : Fin c → X) (y : Fin c → Y) : PMF (P.Pub × List Bool) :=
  condLaw (lookupLaw μ P) {ω | xs ω = x ∧ ys ω = y} transcript

/-- `Q^{û,v̂}_{x,y} = Π^{x,y,û,v̂}` (p.9): the law of the transcript conditioned on `X = x`,
`Y = y`, `U_ℓ = û`, `V_ℓ = v̂`, where `ℓ = L(x, y)`, `U_ℓ = E_ℓ(U)` and `V_ℓ = E_ℓ(V)`. -/
noncomputable def Qhat (F : PartialFn X Y) (μ : PMF (X × Y))
    (P : RandProtocol ((Fin c → X) × (Fin (4 * b) → ZMod 2)) ((Fin c → Y) × (Fin (4 * b) → ZMod 2)))
    (E : (Fin c → ZMod 2) → (Fin (4 * b) → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2))
    (x : Fin c → X) (y : Fin c → Y) (uh vh : Fin b → ZMod 2) : PMF (P.Pub × List Bool) :=
  condLaw (lookupLaw μ P)
    {ω | xs ω = x ∧ ys ω = y ∧ E (addr F x y) (U ω) = uh ∧ E (addr F x y) (V ω) = vh} transcript

end QCSepTotal



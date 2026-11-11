-- Prove2me | Definitions.Def_KAQROM_Oracle
-- name    : KAQROM_Oracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:35.774696+00:00
-- url     : https://prove2.me/theorems/5f3979fd-d28e-4795-95a2-2ee175b87701
-- title:
--   Random oracles $H:X\to\{0,1\}^\ell$, partial oracles, transcripts, $\mathcal H(h,\tau)$, reprogramming $H[\tau]$, and $U_H$
-- statement:
--   Fix a finite set $X$ and $Y=\{0,1\}^\ell$. The **oracle space** $\mathcal H$ is the finite set of all functions $H:X\to Y$; $H\leftarrow\mathcal H$ is the uniform distribution.
--
--   1. A **partial oracle** is a function $h:\mathrm{Dom}(h)\to Y$ with $\mathrm{Dom}(h)\subseteq X$. We write $h\preceq H$ when $H(x)=h(x)$ for every $x\in\mathrm{Dom}(h)$.
--   2. An **ordered transcript** $\tau=((x_1,y_1),\dots,(x_t,y_t))$ keeps repeated queries; $|\tau|=t$, and $\mathrm{Dom}(\tau)$ is the set of distinct queried points. It is consistent when $x_i=x_j$ implies $y_i=y_j$, and then defines the partial oracle $\tau(x_i)=y_i$. We write $\tau\preceq H$ when every recorded pair agrees with $H$.
--   3. $\mathcal H(h,\tau_1,\dots,\tau_k)=\{H\in\mathcal H: h\preceq H,\ \tau_j\preceq H\ \forall j\}$.
--   4. The **reprogrammed oracle** is $H[\tau](x)=\tau(x)$ for $x\in\mathrm{Dom}(\tau)$ and $H(x)$ otherwise; successive reprogramming $H[\tau][\tau']$ lets $\tau'$ overwrite $\tau$ on their common domain.
--   5. The **oracle unitary** acts on a query register $X$, a response register $Y$ and a work register $W$ by
--   $$
--   U_H|x\rangle|y\rangle|w\rangle=|x\rangle|y\oplus H(x)\rangle|w\rangle .
--   $$
--
--   These are the objects of §§3–3.4 of the source on which every protocol, attack and hybrid of the mission is built.
--
--   **Formalization Note** $Y$ is the type of bit strings `Fin ℓ → ZMod 2`, so XOR is addition. A partial oracle is a map $X\to Y\cup\{\text{none}\}$. The partial oracle of a transcript takes the first recorded answer at each point, which is the answer when the transcript is consistent. $U_H$ is the permutation matrix of $(x,y,w)\mapsto(x,y+H(x),w)$.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), §3 preamble, p.16; Definition 3.1, p.16; Definition 3.3, p.17; §3.4 and Definition 3.4, p.18

import Mathlib

namespace KAQROM

open Matrix

/-- The response set `Y = {0,1}^ℓ`, as bit strings `Fin ℓ → ZMod 2`; XOR is `+`. -/
abbrev Bits (ℓ : ℕ) := Fin ℓ → ZMod 2

/-- A **random-oracle function** `H : X → Y` with `Y = {0,1}^ℓ`; the oracle space `ℋ` is the
finite type of all such functions, and `H ← ℋ` is the uniform distribution on it.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), §3 preamble,
p.16; Definitions 3.3 and 3.4, pp.17–18; Definition 3.1, p.16.

**Formalization Note.** The security parameter `λ` is fixed throughout; `X` is any finite type
(the paper's `{0,1}^{n(λ)}`), `Y` is `{0,1}^ℓ` for any `ℓ`. -/
abbrev Oracle (X : Type) (ℓ : ℕ) := X → Bits ℓ

/-- A **partial oracle** `h : Dom(h) → Y` (Definition 3.3, p.17), as `X → Option Y`; `Dom(h)` is
the set of `x` with `h x ≠ none`. -/
abbrev PartialOracle (X : Type) (ℓ : ℕ) := X → Option (Bits ℓ)

/-- An **ordered query–answer transcript** `τ = ((x₁,y₁),…,(x_t,y_t))` (§3.4, p.18). Repeated
queries are kept; its length `|τ|` counts them. -/
abbrev Transcript (X : Type) (ℓ : ℕ) := List (X × Bits ℓ)

/-- `h ⪯ H`: the full oracle `H` extends the partial oracle `h` (Definition 3.3, p.17). -/
def PartialOracle.Le {X : Type} {ℓ : ℕ} (h : PartialOracle X ℓ) (H : Oracle X ℓ) : Prop :=
  ∀ x y, h x = some y → H x = y

/-- `τ ⪯ H`: every recorded pair of the transcript `τ` agrees with `H`. -/
def Transcript.Le {X : Type} {ℓ : ℕ} (τ : Transcript X ℓ) (H : Oracle X ℓ) : Prop :=
  ∀ p ∈ τ, H p.1 = p.2

/-- `Dom(τ)`: the set of distinct queried points of a transcript (§3.4, p.18). -/
def Transcript.dom {X : Type} [DecidableEq X] {ℓ : ℕ} (τ : Transcript X ℓ) : Finset X :=
  (τ.map Prod.fst).toFinset

/-- A transcript is **consistent** when `xᵢ = xⱼ` implies `yᵢ = yⱼ` (§3.4, p.18). -/
def Transcript.Consistent {X : Type} {ℓ : ℕ} (τ : Transcript X ℓ) : Prop :=
  ∀ p ∈ τ, ∀ p' ∈ τ, p.1 = p'.1 → p.2 = p'.2

/-- The partial oracle `τ(xᵢ) = yᵢ` defined by a transcript (§3.4, p.18): the answer of the first
recorded pair at `x` (all recorded answers at `x` agree when `τ` is consistent). -/
def Transcript.toPartial {X : Type} [DecidableEq X] {ℓ : ℕ} (τ : Transcript X ℓ) :
    PartialOracle X ℓ :=
  fun x => (τ.find? (fun p => decide (p.1 = x))).map Prod.snd

/-- The set `ℋ(h, τ₁, …, τ_k)` of full oracles that extend the partial oracle `h` and agree with
every transcript `τᵢ` (Definition 3.3, p.17; `ℋ(h)` is the case of the empty list). -/
noncomputable def oraclesExt {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ}
    (h : PartialOracle X ℓ) (τs : List (Transcript X ℓ)) : Finset (Oracle X ℓ) := by
  classical
  exact Finset.univ.filter (fun H => h.Le H ∧ ∀ τ ∈ τs, τ.Le H)

/-- The **reprogrammed oracle** `H[R]` by a partial function `R` (Definition 3.4, p.18):
`H[R](x) = R(x)` for `x ∈ Dom(R)` and `H(x)` otherwise. -/
def reprogramP {X : Type} {ℓ : ℕ} (H : Oracle X ℓ) (R : PartialOracle X ℓ) : Oracle X ℓ :=
  fun x => (R x).getD (H x)

/-- The **reprogrammed oracle** `H[τ]` by a transcript (Definition 3.4, p.18). Successive
reprogramming `H[τ][τ']` is `reprogram (reprogram H τ) τ'`. -/
def reprogram {X : Type} [DecidableEq X] {ℓ : ℕ} (H : Oracle X ℓ) (τ : Transcript X ℓ) :
    Oracle X ℓ :=
  reprogramP H τ.toPartial

/-- The **oracle unitary** `U_H |x⟩|y⟩|w⟩ = |x⟩|y ⊕ H(x)⟩|w⟩` on the query register `X`, response
register `Y = {0,1}^ℓ` and work register `W` (Definition 3.1, p.16), as the permutation matrix
whose column `(x,y,w)` has its one at row `(x, y + H x, w)`. -/
def oracleUnitary {X : Type} [DecidableEq X] {ℓ : ℕ} (H : Oracle X ℓ) (W : Type)
    [DecidableEq W] : Matrix (X × Bits ℓ × W) (X × Bits ℓ × W) ℂ :=
  fun a b => if a = (b.1, b.2.1 + H b.1, b.2.2) then 1 else 0

end KAQROM



-- Prove2me | Definitions.Def_QCSepTotal_Ftot
-- name    : QCSepTotal_Ftot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:33:13.481601+00:00
-- url     : https://prove2.me/theorems/97e1e2f0-644d-47d0-8057-3104b1a81677
-- title:
--   The total function $F_{\mathrm{tot}}$ of eq. (5), $D_c$, the address $L(x,y)$ and padded certificates
-- statement:
--   Let $F$ be a partial function on $X\times Y$, let $c,b\ge1$, let $E_\ell:\mathbb F_2^{4b}\to\mathbb F_2^{b}$ ($\ell\in\mathbb F_2^c$) be the fixed-seed maps of an extractor, linear over $\mathbb F_2$, and let $V(x,y;p)$ be a predicate on $b$-bit certificates. For tuples $x=(x_1,\dots,x_c)$ and $y=(y_1,\dots,y_c)$:
--
--   1. $D_c(x,y)=1$ iff every pair $(x_i,y_i)$ lies in $\mathrm{dom}(F)$;
--   2. on that domain, $L(x,y)=(F(x_1,y_1),\dots,F(x_c,y_c))\in\mathbb F_2^c$;
--   3. Alice holds $(x,U)$ and Bob $(y,V)$ with $U,V\in\mathbb F_2^{4b}$, and
--   $$F_{\mathrm{tot}}(x,U;y,V)=\begin{cases}V\bigl(x,y;E_{L(x,y)}(U+V)\bigr)&\text{if }D_c(x,y)=1,\\ 0&\text{if }D_c(x,y)=0;\end{cases}$$
--   4. for $b_0\le b$ and a predicate $V_0$ on $b_0$-bit certificates, the **padded predicate** applies $V_0$ to the first $b_0$ bits of a $b$-bit certificate and ignores the rest.
--
--   This is the construction of Section 3.1: the extractor replaces the lookup table of $2^c$ certificates by the single cell $U+V$.
--
--   **Formalization Note** $\mathbb F_2$ is the integers modulo $2$, so $U+V$ is bitwise XOR. Coordinate $i$ of $L(x,y)$ is $1$ iff $F(x_i,y_i)=1$; it is read only when $D_c(x,y)=1$. The extractor and the certificate predicate are parameters; Section 3.1 instantiates them with Lemma 2.3 and with the padded predicate of Proposition 2.4.
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), §3.1, p.6, eq. (5) and footnote 4

import Mathlib
import Definitions.Def_QCSepTotal_PartialFn

namespace QCSepTotal

variable {X Y : Type}

/-- The tuple-domain predicate `D_c(x, y)` (F. Le Gall, *Improved Separations between Quantum and
Classical Communication Complexity of Total Functions*, arXiv:2609.16726, held version sha256
970e1476…, §3.1, p.6): all `c` pairs `(x_i, y_i)` lie in `dom(F)`. -/
def Dc (F : PartialFn X Y) {c : ℕ} (x : Fin c → X) (y : Fin c → Y) : Bool :=
  decide (∀ i, (F (x i) (y i)).isSome)

/-- The address `L(x, y) = (F(x_1, y_1), …, F(x_c, y_c)) ∈ F₂^c` (§3.1, p.6).

**Formalization Note.** The paper defines `L` only on `D_c`; here coordinate `i` is `1` iff
`F(x_i, y_i) = 1`, which is the paper's value on `D_c`. It is only read on `D_c` (in `Ftot`, and
for pairs in the support of a distribution supported on `dom(F)`). -/
def addr (F : PartialFn X Y) {c : ℕ} (x : Fin c → X) (y : Fin c → Y) : Fin c → ZMod 2 :=
  fun i => if F (x i) (y i) = some true then 1 else 0

/-- The **total function** `Ftot` of eq. (5), p.6. Alice holds `(x, U)` and Bob `(y, V)`, with
`x, y` tuples of `c` inputs and `U, V ∈ F₂^{4b}`:
`Ftot(x, U; y, V) = V(x, y; E_{L(x,y)}(U + V))` if `D_c(x, y) = 1`, and `0` otherwise.
Here `E ℓ` is the fixed-seed map `E_ℓ : F₂^{4b} → F₂^b` of an extractor, linear by type, and
`Vc x y p` is the certificate predicate on `b`-bit certificates.

**Formalization Note.** `F₂` is `ZMod 2`, so `U + V` is bitwise XOR. The extractor and the
certificate predicate are parameters; Section 3.1 instantiates them with Lemma 2.3 and with the
padded predicate of Proposition 2.4 (`padCert`). -/
def Ftot (F : PartialFn X Y) (c b : ℕ)
    (E : (Fin c → ZMod 2) → (Fin (4 * b) → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2))
    (Vc : (Fin c → X) → (Fin c → Y) → (Fin b → ZMod 2) → Bool) :
    ((Fin c → X) × (Fin (4 * b) → ZMod 2)) → ((Fin c → Y) × (Fin (4 * b) → ZMod 2)) → Bool :=
  fun xU yV =>
    if Dc F xU.1 yV.1 then Vc xU.1 yV.1 (E (addr F xU.1 yV.1) (xU.2 + yV.2)) else false

/-- The first `b₀` coordinates of a `b`-bit certificate, `b₀ ≤ b`. -/
def truncCert {b₀ b : ℕ} (h : b₀ ≤ b) (p : Fin b → ZMod 2) : Fin b₀ → ZMod 2 :=
  fun i => p (Fin.castLE h i)

/-- The **padded certificate predicate** of §3.1, p.6: "Define `V(x, y; p)` on `b`-bit
certificates by applying the original predicate to the first `b₀` bits and ignoring the remaining
bits." -/
def padCert {Z : Type} {b₀ b : ℕ} (h : b₀ ≤ b) (V₀ : Z → (Fin b₀ → ZMod 2) → Bool) :
    Z → (Fin b → ZMod 2) → Bool :=
  fun z p => V₀ z (truncCert h p)

end QCSepTotal



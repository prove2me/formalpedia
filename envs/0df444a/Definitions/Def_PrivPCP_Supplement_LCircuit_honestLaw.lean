-- Prove2me | Definitions.Def_PrivPCP_Supplement_LCircuit_honestLaw
-- name    : PrivPCP_Supplement_LCircuit_honestLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:53:56.005142+00:00
-- url     : https://prove2.me/theorems/ce244529-b0da-464e-b6b2-210615ab1b43
-- title:
--   The honest execution $\mathrm{Tr}_C(x)$ of a circuit with prescribed auxiliary and random-word laws
-- statement:
--   Let $C$ be a layered computation circuit over $\mathbb F_q$, $\mu_0$ a law of the input $W_0$, $R_\ell$ a prescribed law of the random block of layer $\ell$ for each $\ell$, and $P$ an **honest prover**: for each layer $\ell$, a law $P_\ell(t)$ of the auxiliary words of layer $\ell$ given the transcript $t$ so far.
--
--   The **honest execution** draws $W_0\sim\mu_0$ and then, for $\ell=1,\dots,L$, draws the auxiliary words $\Pi_\ell\sim P_\ell(t)$, where $t$ holds the input and the wires of the layers before $\ell$, draws the random words of layer $\ell$ fresh from $R_\ell$ (independently of everything drawn so far), and lets every gate of layer $\ell$ evaluate correctly on its input block $(W_{\ell-1},\Pi_\ell,R_\ell)$. Its law on transcripts is $\mathrm{Tr}_C(x)$ when $\mu_0=\mathcal C_x$ and $P$ is the prover for $x$.
--
--   **Formalization Note** "$R_\ell$ consists of fresh random words independent of $x$ and of one another. The construction specifies their honest distributions" (p.27): the law of each layer's random block is the construction's choice and does not depend on $x$, and different layers' blocks are independent. The construction delimits the words inside one block, so their mutual independence is a property of the law it chooses. At layer $\ell$ the prover sees only the input and the earlier layers (the transcript is $0$ on layer $\ell$ and later), so it is causal by construction.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Definition 5.3, pp.27–28 (PDF pp.29–30)

import Mathlib
import Definitions.Def_PrivPCP_Supplement_LCircuit

set_option autoImplicit false

namespace PrivPCP.Supplement

namespace LCircuit

variable (C : LCircuit)

/-- The transcript with input `w₀` and zeros on every other wire (not yet filled). -/
def initT {q : ℕ} (w₀ : Fin C.N0 → ZMod q) : C.Coord → ZMod q
  | Sum.inl j => w₀ j
  | _ => 0

/-- Fill layer `ℓ`: write the auxiliary words `π` and the random words `r` of layer `ℓ`, then let
every gate of layer `ℓ` evaluate on its input block. -/
def fillLayer {q : ℕ} (ℓ : Fin C.L) (t : C.Coord → ZMod q) (π : C.AuxIdx → ZMod q)
    (r : Fin (C.layer ℓ).rndLen → ZMod q) : C.Coord → ZMod q :=
  let t₁ : C.Coord → ZMod q := fun c =>
    match c with
    | Sum.inr (Sum.inl a) => if a.1 = ℓ then π a else t c
    | Sum.inr (Sum.inr (Sum.inl i)) =>
        if h : i.1 = ℓ then r (Fin.cast (by rw [h]) i.2) else t c
    | _ => t c
  fun c =>
    match c with
    | Sum.inr (Sum.inr (Sum.inr o)) => if o.1 = ℓ then C.gateVal t₁ o else t₁ c
    | _ => t₁ c

/-- The law of the **honest execution** `Tr_C(x)` (Bafna, Vyas, *Private PCPs from Product
Expansion*, STOC 2027 submission manuscript (sha256 c2cac1e0…), Definition 5.3, p.27 and (2), p.28):
the input `W_0` is drawn from `μ₀` (the encoding law `C_x`); then, layer by layer, the prover draws
the auxiliary words `Π_ℓ` of layer `ℓ` from `P ℓ t`, the random words `R_ℓ` of layer `ℓ` are drawn
fresh from their prescribed law `R ℓ`, and every computation gate of layer `ℓ` evaluates correctly on
its input block `(W_{ℓ−1}, Π_ℓ, R_ℓ)`.

**Formalization Note** "`R_ℓ` consists of fresh random words independent of `x` and of one another.
The construction specifies their honest distributions" (p.27): `R ℓ` is any law on the random block
of layer `ℓ` (the construction's choice; it does not depend on `x`), drawn independently of the input,
of the auxiliary words and of every other layer's random block. The words inside one layer's block
are the construction's to delimit, so their mutual independence is a property of the law `R ℓ` the
construction chooses. The transcript `t` passed to the prover at layer `ℓ` carries the input and the
wires of the earlier layers and is `0` on layer `ℓ` and later, so the prover is causal: it never sees
the current or later random words. -/
noncomputable def honestLaw {q : ℕ} [NeZero q] (μ₀ : PMF (Fin C.N0 → ZMod q))
    (R : (ℓ : Fin C.L) → PMF (Fin (C.layer ℓ).rndLen → ZMod q))
    (P : Fin C.L → (C.Coord → ZMod q) → PMF (C.AuxIdx → ZMod q)) : PMF (C.Coord → ZMod q) :=
  (List.finRange C.L).foldl
    (fun acc ℓ => acc.bind fun t => (P ℓ t).bind fun π => (R ℓ).map (C.fillLayer ℓ t π))
    (μ₀.map C.initT)

end LCircuit

end PrivPCP.Supplement



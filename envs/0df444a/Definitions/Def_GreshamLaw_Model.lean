-- Prove2me | Definitions.Def_GreshamLaw_Model
-- name    : GreshamLaw_Model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:28:15.492727+00:00
-- url     : https://prove2.me/theorems/c0e96c0f-f7ea-4879-b32f-2ad1dd74d7db
-- title:
--   Coins under legal tender: face value, melt value, legal and optimal payments
-- statement:
--   This file fixes the vocabulary of a minimal model of coins under legal tender law.
--
--   1. **Coin.** A coin $c$ has a *face value* $f_c\in\mathbb R$ (the nominal value at which legal tender law requires it to be accepted) and a *melt value* $m_c\in\mathbb R$ (the market value of its metal).
--   2. **Totals.** For a family of coins $(c_i)_{i\in\iota}$ and a finite set $P\subseteq\iota$: $F(P)=\sum_{i\in P} f_{c_i}$ and $M(P)=\sum_{i\in P} m_{c_i}$.
--   3. **Legal tender at equal value.** A wallet $s$ satisfies it when $f_{c_i}=f_{c_j}$ for all $i,j\in s$.
--   4. **Legal payment.** $P$ is a legal payment of the debt $d$ from $s$ when $P\subseteq s$ and $F(P)=d$.
--   5. **Optimal payment.** A legal payment $P$ of $d$ is optimal when every legal payment $Q$ of $d$ from $s$ satisfies $$M(s\setminus Q)\le M(s\setminus P),$$ i.e. the payer retains as much intrinsic value as possible.
--   6. **Acceptance at market value.** Without legal tender, a seller accepts $P$ for the price $p$ when $p\le M(P)$.
--   7. **Arbitrage round.** For a legal rate $r$ (shillings per guinea at home) and a foreign rate $m$ (shillings' worth of silver buying one guinea's gold abroad), $$A_{r,m}(N)=\frac{N}{m}\,r .$$
--
--   These notions formalize the article's sections "Good money and bad money", "Theory" and the 1717 gold-standard episode.
--
--   **Formalization Note** Wallets are finite sets of indices, so distinct coins with equal values remain distinct. In $A_{r,m}$, division by $m=0$ returns $0$ in Lean; statements using it assume $m>0$.
-- source:
--   Wikipedia, "Gresham's law" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Gresham%27s_law, sections "Good money and bad money", "Theory", "Reverse of Gresham's law (Thiers' law)"

import Mathlib

namespace GreshamLaw

/-- A coin, described by its *face value* (the nominal value at which legal tender law
requires it to be accepted) and its *melt value* (the market value of the metal it
contains, i.e. its intrinsic or commodity value). -/
structure Coin where
  face : ℝ
  melt : ℝ

/-- Total face value of the coins indexed by the finite set `P`. -/
def totalFace {ι : Type*} (coin : ι → Coin) (P : Finset ι) : ℝ :=
  ∑ i ∈ P, (coin i).face

/-- Total melt (intrinsic) value of the coins indexed by the finite set `P`. -/
def totalMelt {ι : Type*} (coin : ι → Coin) (P : Finset ι) : ℝ :=
  ∑ i ∈ P, (coin i).melt

/-- Legal tender at equal value: all coins of the wallet `s` carry the same face value, so
the law requires each of them to be accepted at the same value. -/
def EqualLegalTender {ι : Type*} (coin : ι → Coin) (s : Finset ι) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, (coin i).face = (coin j).face

/-- Under legal tender law a creditor must accept coins at face value, so a set `P` of coins
taken from the wallet `s` settles a debt of `d` exactly when its total face value is `d`. -/
def IsLegalPayment {ι : Type*} (coin : ι → Coin) (s P : Finset ι) (d : ℝ) : Prop :=
  P ⊆ s ∧ totalFace coin P = d

/-- A legal payment of the debt `d` out of the wallet `s` is *optimal* for the payer when no
other legal payment of `d` out of `s` lets the payer keep more intrinsic value: the payer
"prefers to save the intrinsically more valuable money". -/
def IsOptimalPayment {ι : Type*} [DecidableEq ι] (coin : ι → Coin) (s P : Finset ι) (d : ℝ) : Prop :=
  IsLegalPayment coin s P d ∧
    ∀ Q : Finset ι, IsLegalPayment coin s Q d → totalMelt coin (s \ Q) ≤ totalMelt coin (s \ P)

/-- In the absence of legal tender law a seller values coins only by their intrinsic
content, and accepts the coins `P` for a good of price `p` exactly when their total melt
value is at least `p`. -/
def AcceptsAtMarketValue {ι : Type*} (coin : ι → Coin) (P : Finset ι) (p : ℝ) : Prop :=
  p ≤ totalMelt coin P

/-- One round of the bimetallic arbitrage described for Britain after 1717.  The legal
rate at home is `r` silver shillings per gold guinea; abroad, the gold contained in one
guinea costs the silver contained in `m` shillings.  Starting with `N` shillings, a trader
ships the silver abroad, buys the gold of `N / m` guineas, has it coined at home, and buys
`(N / m) * r` shillings with those guineas at the legal rate.  Transport and minting costs
are ignored. -/
noncomputable def arbitrageRound (r m N : ℝ) : ℝ :=
  N / m * r

end GreshamLaw



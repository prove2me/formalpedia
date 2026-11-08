-- Prove2me | Definitions.Def_MantriCVQ_Seed
-- name    : MantriCVQ_Seed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:08.145194+00:00
-- url     : https://prove2.me/theorems/cff57773-b4ff-43d0-a7be-edd375108cb4
-- title:
--   Seeds of the random projections and generation of leaf tables
-- statement:
--   The **seed** of a tree holds, at each node, a secret $S\in\mathbb F_2^m$ and a table of bits for the data entries. Under the uniform distribution on seeds, the secrets and bits are independent and uniform across nodes. The **generated leaf table** $X_v$ from a prescribed root value $v$ is defined from the root down: at a node with prescribed value $v'$, secret $S$ and bits $f$, the code child $x$ is prescribed $C_m(S,x)$, the data child $y\ne S$ is prescribed $f(y)$, and the free child $S$ is prescribed $v'$. The **free leaf** is reached by descending into the free child at every level. The same seed with root values $0$ and $1$ gives the coupled pair $(X_0,X_1)$.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §4.2, p. 17 (PDF p. 19), Eq. (4.4)

import Mathlib
import Definitions.Def_MantriCVQ_Addr

open QAlgorithms.Complexity

namespace MantriCVQ

/-- The seed of the random projections of a tree whose nodes have the listed dimensions (Mantri,
arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §4.2, p. 17 (PDF p. 19)): at the root, a secret `S` and
a table of bits for the data entries (the entry at `S` is unused), and a seed for each code and data
child. Under the uniform distribution on seeds, the secrets and the bits are independent and uniform,
and the projections of distinct nodes are independent. -/
def Seed : List ℕ → Type
  | [] => Unit
  | m :: ms => (Bits m × (Bits m → Bool)) × (Bool → Bits m → Seed ms)

instance instFintypeSeed : ∀ ms : List ℕ, Fintype (Seed ms)
  | [] => inferInstanceAs (Fintype Unit)
  | m :: ms =>
    letI := instFintypeSeed ms
    inferInstanceAs (Fintype ((Bits m × (Bits m → Bool)) × (Bool → Bits m → Seed ms)))

instance instDecidableEqSeed : ∀ ms : List ℕ, DecidableEq (Seed ms)
  | [] => inferInstanceAs (DecidableEq Unit)
  | m :: ms =>
    letI := instDecidableEqSeed ms
    inferInstanceAs (DecidableEq ((Bits m × (Bits m → Bool)) × (Bool → Bits m → Seed ms)))

/-- The leaf table generated from the prescribed root value `v` with the seed `s` (§4.2, p. 17, Eq.
(4.4); p. 5 (PDF p. 7)): at a node with secret `S` and bits `f`, the code child `x` is prescribed
`C_m(S, x)`, the data child `y ≠ S` is prescribed `f y`, and the free child `S` is prescribed the
node's own value. At a leaf, the table holds the prescribed value. -/
def gen (C : (m : ℕ) → Bits m → Bits m → Bool) :
    (ms : List ℕ) → Seed ms → Bool → Addr ms → Bool
  | [], _, v, _ => v
  | m :: ms, ((S, f), kids), v, (b, x, a) =>
    gen C ms (kids b x) (if b then (if x = S then v else f x) else C m S x) a

/-- The free leaf of a tree (§4.2, p. 17): reached from the root by descending into the free child at
every level. -/
def freeLeaf : (ms : List ℕ) → Seed ms → Addr ms
  | [], _ => ()
  | _ :: ms, ((S, _), kids) => (true, S, freeLeaf ms (kids true S))

end MantriCVQ



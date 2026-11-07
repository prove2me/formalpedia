-- Prove2me | solution 1 for AaronsonAmbainis.blockInequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:32:32.369189+00:00
-- url     : https://prove2.me/submissions/140bd297-45fa-4cf1-9064-0b527427b3e0

import Definitions.Def_AaronsonAmbainis_Row_Markov
import Definitions.Def_AaronsonAmbainis_Row_Block
import Definitions.Def_AaronsonAmbainis_Row_Main
import Theorems.Thm_AaronsonAmbainis_blockInequality_of_markov
import Theorems.Thm_AaronsonAmbainis_markovEndpoint


set_option autoImplicit true
open AaronsonAmbainis
namespace AaronsonAmbainis
theorem _root_.solution : BlockInequality := blockInequality_of_markov markovEndpoint
end AaronsonAmbainis
